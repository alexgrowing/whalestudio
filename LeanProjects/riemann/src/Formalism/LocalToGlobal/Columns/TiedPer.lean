import Formalism.LocalToGlobal.Columns.TiedValFi
import Formalism.LocalToGlobal.Columns.RecordInst

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

namespace GSD.Ev

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K} {σ : K →+* ℂ} (E : S.Ev σ)

theorem sharp_mem (ℓ : S.V →ₛₗ[σ] ℂ) : E.sharp ℓ ∈ Submodule.span ℂ (Set.range E.ev) :=
  Submodule.sum_mem _ fun _ _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem ip_sharp_ev (hG : IsUnit E.gram.det) (ℓ : S.V →ₛₗ[σ] ℂ) (x : S.V) : E.ip (E.sharp ℓ) (E.ev x) = ℓ x := by
  rw [← E.extend_eq_ip hG, E.extend_ev]

theorem eq_of_ip_ev (hG : IsUnit E.gram.det) {f f' : E.Y → ℂ} (hf : f ∈ Submodule.span ℂ (Set.range E.ev))
    (hf' : f' ∈ Submodule.span ℂ (Set.range E.ev)) (h : ∀ x, E.ip f (E.ev x) = E.ip f' (E.ev x)) : f = f' := by
  obtain ⟨z, rfl⟩ := E.span_ev_le_range_lin hf
  obtain ⟨z', rfl⟩ := E.span_ev_le_range_lin hf'
  congr 1
  have key : ∀ (w : S.ιV → ℂ) (j : S.ιV),
      E.ip (E.lin w) (E.ev (S.bV j)) = ((fun i => starRingEnd ℂ (w i)) ᵥ* E.gram) j := by
    intro w j
    simp only [lin, Fintype.linearCombination_apply, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, Matrix.vecMul, dotProduct, gram, Matrix.of_apply]
  have h1 : (fun i => starRingEnd ℂ (z i)) ᵥ* E.gram = (fun i => starRingEnd ℂ (z' i)) ᵥ* E.gram := by
    funext j
    rw [← key, ← key]
    exact h _
  have h2 := congrArg (fun v => v ᵥ* E.gram⁻¹) h1
  simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hG, Matrix.vecMul_one] at h2
  funext i
  exact (starRingEnd ℂ).injective (congrFun h2 i)

theorem tr_mem_span (g : S.G) {f : E.Y → ℂ} (hf : f ∈ Submodule.span ℂ (Set.range E.ev)) :
    E.tr g f ∈ Submodule.span ℂ (Set.range E.ev) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [E.tr_ev]
    exact Submodule.subset_span ⟨_, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem ip_tr_ev (h : S.Ok) (g : S.G) {f : E.Y → ℂ} (hf : f ∈ Submodule.span ℂ (Set.range E.ev)) (x : S.V) :
    E.ip (E.tr g f) (E.ev (S.ρ g x)) = E.ip f (E.ev x) := by
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    rw [E.tr_ev, E.ip_ev, E.ip_ev, h.inv]
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add y y' _ _ hy hy' => rw [map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hy, hy']
  | smul a y _ hy => rw [map_smul, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, LinearMap.smul_apply, LinearMap.smul_apply, hy]

theorem tr_sharp (h : S.Ok) (hG : IsUnit E.gram.det) (g : S.G) (ℓ : S.V →ₛₗ[σ] ℂ) (hℓ : ∀ x, ℓ (S.ρ g x) = ℓ x) :
    E.tr g (E.sharp ℓ) = E.sharp ℓ := by
  refine E.eq_of_ip_ev hG (E.tr_mem_span g (E.sharp_mem ℓ)) (E.sharp_mem ℓ) fun x => ?_
  have e : S.ρ g (S.ρ g⁻¹ x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [E.ip_sharp_ev hG]
  conv_lhs => rw [← e]
  rw [E.ip_tr_ev h g (E.sharp_mem ℓ), E.ip_sharp_ev hG, ← hℓ, e]

end GSD.Ev

namespace GSD

variable {K : Type} [Field K] [NumberField K] [StarRing K]

structure Dua (S S' : GSD K) where
  eG : S.G ≃ S'.G
  eD : S.D ≃ S'.D
  smul : ∀ (g : S.G) (d : S.D), eD (g • d) = eG g • eD d

  B : S.V →ₗ[K] S'.V →ₗ[K] K
  inv : ∀ (g : S.G) (x : S.V) (y : S'.V), B (S.ρ g x) (S'.ρ (eG g) y) = B x y
  repr : ∀ ℓ : S.V →ₗ[K] K, ∃ y : S'.V, ∀ x, B x y = ℓ x
  ext : ∀ y y' : S'.V, (∀ x, B x y = B x y') → y = y'

namespace Dua

variable {S S' : GSD K} (P : Dua S S') (σ : K →+* ℂ)

def semi (y : S'.V) : S.V →ₛₗ[σ] ℂ where
  toFun x := σ (P.B x y)
  map_add' x x' := by rw [map_add, LinearMap.add_apply, map_add]
  map_smul' a x := by rw [map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, smul_eq_mul]

theorem semi_apply (y : S'.V) (x : S.V) : P.semi σ y x = σ (P.B x y) := rfl

theorem rho_rho_inv (g : S.G) (x : S.V) : S.ρ g (S.ρ g⁻¹ x) = x := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem partner (h : S.Ok) (φ : S.EqFun) :
    ∃ ψ : S'.EqFun, ∀ (d : S.D) (x : S.V), P.B x ((ψ : S'.D → S'.V) (P.eD d)) = S.pair ((φ : S.D → S.V) d) x := by
  choose θ hθ using fun v : S.V => P.repr (S.pair v)
  refine ⟨⟨fun d' => θ ((φ : S.D → S.V) (P.eD.symm d')), fun g' d' => ?_⟩, fun d x => ?_⟩
  · apply P.ext
    intro x
    have e0 : P.eD.symm (g' • d') = P.eG.symm g' • P.eD.symm d' := by
      rw [Equiv.symm_apply_eq, P.smul, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    show P.B x (θ ((φ : S.D → S.V) (P.eD.symm (g' • d')))) = P.B x (S'.ρ g' (θ ((φ : S.D → S.V) (P.eD.symm d'))))
    rw [hθ, e0, φ.2]
    conv_lhs => rw [← rho_rho_inv (P.eG.symm g') x]
    rw [h.inv, ← hθ, ← P.inv (P.eG.symm g'), rho_rho_inv, Equiv.apply_symm_apply]
  · show P.B x (θ ((φ : S.D → S.V) (P.eD.symm (P.eD d)))) = _
    rw [hθ, Equiv.symm_apply_apply]

variable {σ} (E : S.Ev σ) {ι : Type} [Fintype ι]

def jOf (b : ι → S'.EqFun) (z : ι → ℂ) : S.Cl → E.Y → ℂ :=
  fun c => ∑ a, starRingEnd ℂ (z a) • E.sharp (P.semi σ ((b a : S'.D → S'.V) (P.eD (S.outSec.rep c))))

theorem jOf_mem (b : ι → S'.EqFun) (z : ι → ℂ) (c : S.Cl) : P.jOf E b z c ∈ Submodule.span ℂ (Set.range E.ev) :=
  Submodule.sum_mem _ fun _ _ => Submodule.smul_mem _ _ (E.sharp_mem _)

theorem ip_jOf (hG : IsUnit E.gram.det) (b : ι → S'.EqFun) (z : ι → ℂ) (c : S.Cl) (x : S.V) :
    E.ip (P.jOf E b z c) (E.ev x) = ∑ a, z a * σ (P.B x ((b a : S'.D → S'.V) (P.eD (S.outSec.rep c)))) := by
  simp only [jOf, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, Complex.conj_conj, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [E.ip_sharp_ev hG, semi_apply]

theorem jOf_mem_Fi (h : S.Ok) (hG : IsUnit E.gram.det) (b : ι → S'.EqFun) (z : ι → ℂ) : P.jOf E b z ∈ E.Fi := by
  rw [E.mem_Fi_iff h]
  intro c
  refine ⟨P.jOf_mem E b z c, fun γ hγ => ?_⟩
  unfold jOf
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul]
  congr 1
  refine E.tr_sharp h hG γ _ fun x => ?_
  rw [semi_apply, semi_apply]
  congr 1
  have e1 := (b a).2 (P.eG γ) (P.eD (S.outSec.rep c))
  rw [← P.smul, MulAction.mem_stabilizer_iff.1 hγ] at e1
  conv_lhs => rw [e1]
  exact P.inv γ x _

theorem jOf_partner (h : S.Ok) (hG : IsUnit E.gram.det) (b : Basis ι K S'.EqFun) (φ : S.EqFun) :
    ∃ z, P.jOf E b z = E.emb φ := by
  obtain ⟨ψ, hψ⟩ := P.partner h φ
  refine ⟨fun a => σ (b.repr ψ a), ?_⟩
  funext c
  refine E.eq_of_ip_ev hG (P.jOf_mem E b _ c) (Submodule.subset_span ⟨_, rfl⟩) fun x => ?_
  rw [P.ip_jOf E hG, E.emb_apply, E.ip_ev, ← hψ]
  conv_rhs => rw [← b.sum_repr ψ]
  simp only [← map_mul, ← map_sum]
  congr 1
  rw [Submodule.coe_sum, Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul]

theorem jOf_add (b : ι → S'.EqFun) (z z' : ι → ℂ) : P.jOf E b (z + z') = P.jOf E b z + P.jOf E b z' := by
  funext c
  simp only [jOf, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]

theorem jOf_smul (b : ι → S'.EqFun) (t : ℂ) (z : ι → ℂ) : P.jOf E b (t • z) = starRingEnd ℂ t • P.jOf E b z := by
  funext c
  simp only [jOf, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]

theorem jOf_onto (h : S.Ok) (hG : IsUnit E.gram.det) (b : Basis ι K S'.EqFun) (F : S.Cl → E.Y → ℂ) (hF : F ∈ E.Fi) :
    ∃ z, P.jOf E b z = F := by
  unfold GSD.Ev.Fi at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, rfl⟩ := hx
    exact P.jOf_partner E h hG b φ
  | zero =>
    refine ⟨0, ?_⟩
    funext c
    simp [jOf]
  | add x y _ _ hx hy =>
    obtain ⟨z, rfl⟩ := hx
    obtain ⟨z', rfl⟩ := hy
    exact ⟨z + z', P.jOf_add E b z z'⟩
  | smul t x _ hx =>
    obtain ⟨z, rfl⟩ := hx
    exact ⟨starRingEnd ℂ t • z, by rw [P.jOf_smul, Complex.conj_conj]⟩

end Dua

end GSD

section Pair

variable {E K : Type} [Field E] [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem per_pair_smul (emb : ι → E →+* K) (lam : ι → DomWeight n) (γ : GL (Fin n) E) (s t : K) (hst : s * t = 1) (x y : VV K lam) :
    pairBK lam (s • rhoVr emb lam γ x) (t • rhoV emb lam γ y) = pairBK lam x y := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [pairingBInvariant_holds, ← mul_assoc, mul_comm t s, hst, one_mul]

theorem per_pair_repr [CharZero K] (lam : ι → DomWeight n) (ℓ : VV K lam →ₗ[K] K) : ∃ y : VV K lam, ∀ x, pairBK lam x y = ℓ x := by
  have hnd := pairingBNondegenerate_holds K ι n lam
  have hinj : Function.Injective (pairBK (K := K) lam).flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact hnd.2 y fun x => LinearMap.congr_fun hy x
  have : FiniteDimensional K (VV K lam) := Module.Finite.of_basis (bVV K lam)
  have hsurj : Function.Surjective (pairBK (K := K) lam).flip :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).1 hinj
  obtain ⟨y, hy⟩ := hsurj ℓ
  exact ⟨y, fun x => by rw [← hy]; rfl⟩

theorem per_pair_ext [CharZero K] (lam : ι → DomWeight n) (y y' : VV K lam) (h : ∀ x, pairBK lam x y = pairBK lam x y') : y = y' := by
  have hnd := pairingBNondegenerate_holds K ι n lam
  rw [← sub_eq_zero]
  exact hnd.2 _ fun x => by rw [map_sub, h x, sub_self]

end Pair

section Xp

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) {SG' : Finset (HeightOneSpectrum (𝓞 X.E))}
  (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

theorem per_chr_mul {n : ℕ} (Λ : LevFam X.E X.K n SG') (h : ↥Λ.grp) :
    ((Λ.inv.chr (⟨h.1, h.2⟩ : ↥Λ.inv.grp) : X.Kˣ) : X.K) * ((Λ.chr h : X.Kˣ) : X.K) = 1 := by
  rw [Λ.inv_chr, ← Units.val_mul, inv_mul_cancel, Units.val_one]

def perDua : GSD.Dua (ptGSD W ΛM) (rowGSD W ΛM) where
  eG := ⟨fun g => (g.1, ⟨g.2.1, g.2.2⟩), fun g => (g.1, ⟨g.2.1, g.2.2⟩), fun _ => rfl, fun _ => rfl⟩
  eD := Equiv.refl _
  smul := fun _ _ => rfl
  B := pairBK W.sgTrue
  inv := fun g x y => per_pair_smul X.emb W.sgTrue (ufGL X.E _ g.1) _ _ (per_chr_mul ΛM ⟨g.2.1, g.2.2⟩) x y
  repr := per_pair_repr W.sgTrue
  ext := per_pair_ext W.sgTrue

variable (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (hM : (rowGSD W ΛM).Ok)

theorem per_jMCL_eq (z : Fin ((rowGSD W ΛM).hDim hM) → ℂ) :
    jMCL W ΛM σ₀ hσ hM z = (perDua W ΛM).jOf (ptEv W ΛM σ₀ hσ) ((rowGSD W ΛM).hB hM) z := rfl

theorem per_jMC_mem_Fi (hX : X.Ok) (z : Fin ((rowGSD W ΛM).hDim hM) → ℂ) :
    jMCL W ΛM σ₀ hσ hM z ∈ (ptEv W ΛM σ₀ hσ).Fi :=
  (perDua W ΛM).jOf_mem_Fi (ptEv W ΛM σ₀ hσ) (ptOk W ΛM hX) (ptEv_gram_unit W ΛM σ₀ hσ) ((rowGSD W ΛM).hB hM) z

theorem per_jMC_onto (hX : X.Ok) (F : (ptGSD W ΛM).Cl → (ptEv W ΛM σ₀ hσ).Y → ℂ) (hF : F ∈ (ptEv W ΛM σ₀ hσ).Fi) :
    ∃ z, jMCL W ΛM σ₀ hσ hM z = F :=
  (perDua W ΛM).jOf_onto (ptEv W ΛM σ₀ hσ) (ptOk W ΛM hX) (ptEv_gram_unit W ΛM σ₀ hσ) ((rowGSD W ΛM).hB hM) F hF

end Xp

end Formalism.L2.Col
