import Formalism.LocalToGlobal.Columns.TiedVal

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

namespace GSD.Ev

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K} {σ : K →+* ℂ} (E : S.Ev σ)

def InvAt (F : S.Cl → E.Y → ℂ) : Prop :=
  ∀ c, F c ∈ Submodule.span ℂ (Set.range E.ev) ∧
    ∀ γ : S.G, γ ∈ MulAction.stabilizer S.G (S.outSec.rep c) → E.tr γ (F c) = F c

theorem invAt_of_mem_Fi {F : S.Cl → E.Y → ℂ} (hF : F ∈ E.Fi) : E.InvAt F := by
  unfold Fi at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, rfl⟩ := hx
    intro c
    refine ⟨Submodule.subset_span ⟨_, rfl⟩, fun γ hγ => ?_⟩
    rw [emb_apply, E.tr_ev, ← φ.2 γ, MulAction.mem_stabilizer_iff.1 hγ]
  | zero => exact fun c => ⟨zero_mem _, fun γ _ => map_zero _⟩
  | add x y _ _ hx hy =>
    exact fun c => ⟨add_mem (hx c).1 (hy c).1, fun γ hγ => by
      rw [Pi.add_apply, map_add, (hx c).2 γ hγ, (hy c).2 γ hγ]⟩
  | smul a x _ hx =>
    exact fun c => ⟨Submodule.smul_mem _ _ (hx c).1, fun γ hγ => by
      rw [Pi.smul_apply, map_smul, (hx c).2 γ hγ]⟩

theorem span_ev_le_range_lin : Submodule.span ℂ (Set.range E.ev) ≤ LinearMap.range E.lin := by
  rw [Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact ⟨_, (E.ev_eq_lin x).symm⟩

open Classical in

def avg (h : S.Ok) (c : S.Cl) : S.V →ₗ[K] S.V :=
  letI := h.fintypeStab (S.outSec.rep c)
  ((Fintype.card (MulAction.stabilizer S.G (S.outSec.rep c)) : K)⁻¹) •
    ∑ γ : MulAction.stabilizer S.G (S.outSec.rep c), S.ρ (γ : S.G)

theorem rho_avg (h : S.Ok) (c : S.Cl) (γ : MulAction.stabilizer S.G (S.outSec.rep c)) (v : S.V) :
    S.ρ (γ : S.G) (avg h c v) = avg h c v := by
  classical
  letI := h.fintypeStab (S.outSec.rep c)
  unfold avg
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft γ) _ _ fun γ' => ?_
  show S.ρ (γ : S.G) (S.ρ (γ' : S.G) v) = S.ρ ((γ * γ' : MulAction.stabilizer S.G (S.outSec.rep c)) : S.G) v
  rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]

theorem ev_avg (h : S.Ok) (c : S.Cl) (v : S.V) :
    letI := h.fintypeStab (S.outSec.rep c)
    E.ev (avg h c v) = ((Fintype.card (MulAction.stabilizer S.G (S.outSec.rep c)) : ℂ)⁻¹) •
      ∑ γ : MulAction.stabilizer S.G (S.outSec.rep c), E.tr (γ : S.G) (E.ev v) := by
  classical
  letI := h.fintypeStab (S.outSec.rep c)
  unfold avg
  rw [LinearMap.smul_apply, LinearMap.map_smulₛₗ, map_inv₀, map_natCast, LinearMap.sum_apply, map_sum]
  congr 1
  exact Finset.sum_congr rfl fun γ _ => (E.tr_ev _ _).symm

open Classical in

def bump (h : S.Ok) (c : S.Cl) (v : S.V) : S.EqFun :=
  (S.resOf h S.outSec).symm ⟨Pi.single c (avg h c v), fun c' γ => by
    by_cases hc : c' = c
    · subst hc
      rw [Pi.single_eq_same]
      exact rho_avg h c' γ v
    · rw [Pi.single_eq_of_ne hc]
      exact map_zero _⟩

open Classical in
theorem emb_bump (h : S.Ok) (c : S.Cl) (v : S.V) (c' : S.Cl) :
    E.emb (bump h c v) c' = if c' = c then E.ev (avg h c v) else 0 := by
  rw [emb_apply, ← S.resOf_apply h S.outSec, bump, LinearEquiv.apply_symm_apply]
  show E.ev ((Pi.single c (avg h c v) : S.Cl → S.V) c') = _
  by_cases hc : c' = c
  · subst hc
    rw [Pi.single_eq_same, if_pos rfl]
  · rw [Pi.single_eq_of_ne hc, if_neg hc, map_zero]

theorem mem_Fi_of_invAt (h : S.Ok) {F : S.Cl → E.Y → ℂ} (hF : E.InvAt F) : F ∈ E.Fi := by
  classical
  letI := h.fintypeCl
  have hz : ∀ c, ∃ z : S.ιV → ℂ, E.lin z = F c := fun c => E.span_ev_le_range_lin (hF c).1
  choose z hz using hz
  have key : F = ∑ c, ∑ i, z c i • E.emb (bump h c (S.bV i)) := by
    funext c'
    rw [Finset.sum_apply, Finset.sum_eq_single c']
    · letI := h.fintypeStab (S.outSec.rep c')
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, emb_bump, if_true, ev_avg]
      have h1 : ∀ i, z c' i • ((Fintype.card (MulAction.stabilizer S.G (S.outSec.rep c')) : ℂ)⁻¹ •
          ∑ γ : MulAction.stabilizer S.G (S.outSec.rep c'), E.tr (γ : S.G) (E.ev (S.bV i))) =
          (Fintype.card (MulAction.stabilizer S.G (S.outSec.rep c')) : ℂ)⁻¹ •
          ∑ γ : MulAction.stabilizer S.G (S.outSec.rep c'), E.tr (γ : S.G) (z c' i • E.ev (S.bV i)) := by
        intro i
        rw [smul_comm, Finset.smul_sum]
        simp only [map_smul]
      simp only [h1]
      rw [← Finset.smul_sum, Finset.sum_comm]
      have h2 : ∀ γ : MulAction.stabilizer S.G (S.outSec.rep c'),
          ∑ i, E.tr (γ : S.G) (z c' i • E.ev (S.bV i)) = F c' := by
        intro γ
        rw [← map_sum]
        have : ∑ i, z c' i • E.ev (S.bV i) = F c' := by
          rw [← hz c']
          simp [lin, Fintype.linearCombination_apply]
        rw [this]
        exact (hF c').2 _ γ.2
      simp only [h2]
      rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀, one_smul]
      exact Nat.cast_ne_zero.2 Fintype.card_ne_zero
    · intro c _ hc
      rw [Finset.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Pi.smul_apply, emb_bump, if_neg (Ne.symm hc), smul_zero]
    · intro hc; exact absurd (Finset.mem_univ c') hc
  rw [key]
  exact Submodule.sum_mem _ fun c _ => Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem mem_Fi_iff (h : S.Ok) (F : S.Cl → E.Y → ℂ) : F ∈ E.Fi ↔ E.InvAt F :=
  ⟨E.invAt_of_mem_Fi, E.mem_Fi_of_invAt h⟩

end GSD.Ev

section Adelic

theorem vfi_ufGL_ratHom {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (n : ℕ) (γ : URat hc n) : ufGL E n (ratHom hc n γ) = (γ : GL (Fin n) E) := by
  show (toGLm E n) (glEquiv (γ : GL (Fin n) E)) = _
  unfold toGLm glEquiv
  simp

variable {X : Fields} {n : ℕ} [NeZero n] {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (hc : CMData X.F X.E) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
  (lam : X.Tau → DomWeight n) (Lf : DecoSet X.E n ST SG → Submodule (𝓞 X.E) (Sp X.E n)) (Λ : LevFam X.E X.K n SG)
  (c₀ : DiaG X.E ST) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 X.F))}
  (L : StepLevel X.F X.E hc.sig (1 : Matrix (Fin n) (Fin n) X.E) T f bad)

structure IsLevOf : Prop where
  U_eq : L.U = levU hc n ST SG Λ.grp
  chi_eq : ∀ (x : L.U) (hx : x.1 ∈ levU hc n ST SG Λ.grp),
    L.chi x = levTyp ((Units.map σ₀.toMonoidHom).comp Λ.chr) ⟨x.1, hx⟩

theorem vfi_frMul_of_isTr (γ : GL (Fin n) X.E) (y y' : FrS X σ₀ n) (h : IsTr (atInf (embAt σ₀ X.emb) γ.1) y' y) :
    frMul σ₀ γ⁻¹ y = y' := by
  have e : y = frMul σ₀ γ y' := Subtype.ext (funext fun τ => h τ)
  rw [e, ← frMul_mul, inv_mul_cancel, frMul_one]

theorem vfi_decoOfD_sm (γ : URat hc n) (κ : levU hc n ST SG Λ.grp) (x : UAd hc n) :
    decoOfD n ST SG c₀ (bc (iA X.F X.E) (γ : GL (Fin n) X.E) * (x : GL (Fin n) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) *
        (κ : GL (Fin n) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F))) =
      ((ratHom hc n γ, levRed hc n ST SG Λ.grp κ⁻¹) : UF X.E n × Λ.grp) •
        decoOfD n ST SG c₀ (x : GL (Fin n) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) := by
  have h := rlc_decoOf_sm hc n ST SG Λ.grp γ κ⁻¹ x
  rw [Subgroup.coe_inv, inv_inv] at h
  unfold decoOfD
  rw [h]
  rfl

theorem vfi_typ (κ : levU hc n ST SG Λ.grp) :
    ((levTyp ((Units.map σ₀.toMonoidHom).comp Λ.chr) κ : ℂˣ) : ℂ) =
      σ₀ ((Λ.chr (levRed hc n ST SG Λ.grp κ⁻¹) : X.Kˣ) : X.K) := by
  unfold levTyp levChr
  rw [MonoidHom.inv_apply, ← map_inv]
  rfl

def adOf (φ : (formGSD (roundPk X lam Lf) Λ).EqFun) :
    UPts hc.sig (1 : Matrix (Fin n) (Fin n) X.E) (FiniteAdeleRing (𝓞 X.F) X.F) → FrS X σ₀ n → ℂ :=
  fun x => (roundEv σ₀ hσ lam Lf Λ).ev ((φ : DecoSet X.E n ST SG → _) (decoOfD n ST SG c₀ x.1))

variable {L}

theorem adOf_mem (hL : IsLevOf hc σ₀ Λ L (ST := ST)) (φ : (formGSD (roundPk X lam Lf) Λ).EqFun) :
    adOf hc σ₀ hσ lam Lf Λ c₀ φ ∈ AdForms L (embAt σ₀ X.emb) lam := by
  refine ⟨?_, fun x _ => evV_mem_ValC X.emb 1 lam σ₀ _⟩
  intro γ hγ x x' κ hx y y' hy
  have hκ : κ.1 ∈ levU hc n ST SG Λ.grp := hL.U_eq ▸ κ.2
  have e := vfi_decoOfD_sm hc Λ c₀ ⟨γ, hγ⟩ ⟨κ.1, hκ⟩ x
  have e2 : decoOfD n ST SG c₀ x'.1 = ((ratHom hc n ⟨γ, hγ⟩, levRed hc n ST SG Λ.grp (⟨κ.1, hκ⟩ : levU hc n ST SG Λ.grp)⁻¹) :
      UF X.E n × Λ.grp) • decoOfD n ST SG c₀ x.1 := by
    rw [hx]; exact e
  show (roundEv σ₀ hσ lam Lf Λ).ev ((φ : DecoSet X.E n ST SG → _) (decoOfD n ST SG c₀ x'.1)) y = _
  rw [e2]
  have e3 := φ.2 ((ratHom hc n ⟨γ, hγ⟩, levRed hc n ST SG Λ.grp (⟨κ.1, hκ⟩ : levU hc n ST SG Λ.grp)⁻¹) : UF X.E n × Λ.grp)
    (decoOfD n ST SG c₀ x.1)
  rw [e3, ← (roundEv σ₀ hσ lam Lf Λ).tr_ev, hL.chi_eq κ hκ, vfi_typ]
  show σ₀ _ • (roundEv σ₀ hσ lam Lf Λ).ev _ (frMul σ₀ (ufGL X.E n (ratHom hc n ⟨γ, hγ⟩))⁻¹ y) = _
  rw [vfi_ufGL_ratHom, vfi_frMul_of_isTr σ₀ γ y y' hy]
  rfl

theorem vfi_isTr_frMul (γ : GL (Fin n) X.E) (z : FrS X σ₀ n) :
    IsTr (atInf (embAt σ₀ X.emb) γ.1) (frMul σ₀ γ⁻¹ z) z := by
  intro τ
  have e : frMul σ₀ γ (frMul σ₀ γ⁻¹ z) = z := by rw [← frMul_mul, mul_inv_cancel, frMul_one]
  exact (congrArg (fun w : FrS X σ₀ n => w.1 τ) e).symm

theorem invAt_of_adForms (hS : DecoPtSurj hc n ST SG) (hL : IsLevOf hc σ₀ Λ L (ST := ST))
    (g : UPts hc.sig (1 : Matrix (Fin n) (Fin n) X.E) (FiniteAdeleRing (𝓞 X.F) X.F) → FrS X σ₀ n → ℂ)
    (hg : g ∈ AdForms L (embAt σ₀ X.emb) lam) :
    (roundEv σ₀ hσ lam Lf Λ).InvAt
      (fun c => g (ptOfD hc n ST SG c₀ ((formGSD (roundPk X lam Lf) Λ).outSec.rep c))) := by
  intro c
  refine ⟨?_, fun a ha => ?_⟩
  · have h1 := hg.2 (ptOfD hc n ST SG c₀ ((formGSD (roundPk X lam Lf) Λ).outSec.rep c)) trivial
    rw [← span_evV X.emb 1 lam σ₀] at h1
    exact h1
  · set yc : UAd hc n := ptOfD hc n ST SG c₀ ((formGSD (roundPk X lam Lf) Λ).outSec.rep c) with hyc
    have h0 : decoOfD n ST SG c₀ (yc : GL (Fin n) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) =
        (formGSD (roundPk X lam Lf) Λ).outSec.rep c := decoOfD_ptOfD hc n ST SG hS c₀ _
    have h1 : decoOf ST SG (yc : GL (Fin n) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) =
        (a : UF X.E n × Λ.grp) • decoOf ST SG (yc : GL (Fin n) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) := by
      apply rla_dia_inj n ST SG c₀
      show decoOfD n ST SG c₀ (yc : GL (Fin n) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) =
        (a : UF X.E n × Λ.grp) • decoOfD n ST SG c₀ (yc : GL (Fin n) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F))
      rw [h0]
      exact (MulAction.mem_stabilizer_iff.1 ha).symm
    obtain ⟨γ, k, hγ, hk, e⟩ := rlc_rel_of_orbit hc n ST SG Λ.grp a h1
    funext z
    show σ₀ ((Λ.chr a.2 : X.Kˣ) : X.K) • g yc (frMul σ₀ (ufGL X.E n a.1)⁻¹ z) = g yc z
    have hk' : ((k⁻¹ : levU hc n ST SG Λ.grp) : GL (Fin n) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)) ∈ L.U := by
      rw [hL.U_eq]; exact (k⁻¹).2
    have h2 := hg.1 γ.1 γ.2 yc yc ⟨_, hk'⟩ (by rw [Subgroup.coe_inv]; exact e) z (frMul σ₀ (γ : GL (Fin n) X.E)⁻¹ z)
      (vfi_isTr_frMul σ₀ γ.1 z)
    rw [h2, hL.chi_eq _ (k⁻¹).2, vfi_typ, inv_inv, hk, ← hγ, vfi_ufGL_ratHom]
    rfl

theorem fi_iff_FiC (hOk : (formGSD (roundPk X lam Lf) Λ).Ok) (hS : DecoPtSurj hc n ST SG) (hL : IsLevOf hc σ₀ Λ L (ST := ST))
    (φ : (formGSD (roundPk X lam Lf) Λ).Cl → FrS X σ₀ n → ℂ) :
    φ ∈ (roundEv σ₀ hσ lam Lf Λ).Fi ↔
      φ ∈ FiC L (embAt σ₀ X.emb) lam
        (fun c => ptOfD hc n ST SG c₀ ((formGSD (roundPk X lam Lf) Λ).outSec.rep c)) := by
  constructor
  · intro h
    refine (Submodule.span_le.2 ?_ : (roundEv σ₀ hσ lam Lf Λ).Fi ≤ _) h
    rintro _ ⟨x, rfl⟩
    refine ⟨adOf hc σ₀ hσ lam Lf Λ c₀ x, adOf_mem hc σ₀ hσ lam Lf Λ c₀ hL x, ?_⟩
    funext c
    show (roundEv σ₀ hσ lam Lf Λ).ev ((x : DecoSet X.E n ST SG → _) (decoOfD n ST SG c₀
      (ptOfD hc n ST SG c₀ ((formGSD (roundPk X lam Lf) Λ).outSec.rep c) : GL (Fin n) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)))) = _
    rw [decoOfD_ptOfD hc n ST SG hS c₀]
    rfl
  · rintro ⟨g, hg, rfl⟩
    exact (roundEv σ₀ hσ lam Lf Λ).mem_Fi_of_invAt hOk (invAt_of_adForms hc σ₀ hσ lam Lf Λ c₀ hS hL g hg)

end Adelic

section Step

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
  (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
  (u : Pr.Word) (i : ℕ) (c₀ : DiaG X.E (Pr.vT u)) (hS : DecoPtSurj hc (R.N i) (Pr.vT u) Pr.vGs)

theorem tieLev_isLevOf {n : ℕ} [NeZero n] (Λ' : LevFam X.E X.K n Pr.vGs) :
    IsLevOf hc σ₀ Λ' (tieLev hc hX hPr σ₀ u Λ') (ST := Pr.vT u) := ⟨rfl, fun _ _ => rfl⟩

theorem Val.fi (Q : ValCrd W Λ σ₀ u i) : Val.Fi W Λ hc hX hPr σ₀ hσ u i c₀ hS Q := by
  obtain ⟨⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩, lt, rfl⟩ := Q
  intro φ
  exact fi_iff_FiC hc σ₀ hσ (W.lamTrue u i) (fun d => d.1.Lsh) (Λ i) c₀ (stepOk W Λ hX u i) hS
    (tieLev_isLevOf hc hX hPr σ₀ u (Λ i)) φ

end Step

end Formalism.L2.Col
