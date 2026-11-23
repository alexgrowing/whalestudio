import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsOperators
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AddHomExtSingle
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGlobalGenerators
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LinearIndependentOfCommSmul

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.WeightIrred

open ThetaReal GlobalGen

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem matrix_mul_of_comp {A M J : Type} [CommRing A] [AddCommGroup M] [Module A M] [Fintype J] (φ : o →+* A)
    (s : J → M) (uniq : ∀ c c' : J → o, ∑ l, φ (c l) • s l = ∑ l, φ (c' l) • s l → c = c')
    {u₁ u₂ u₃ : M ≃ₗ[A] M} {m₁ m₂ m₃ : Matrix J J o} (h₁ : ∀ i, u₁ (s i) = ∑ l, φ (m₁ l i) • s l)
    (h₂ : ∀ i, u₂ (s i) = ∑ l, φ (m₂ l i) • s l) (h₃ : ∀ i, u₃ (s i) = ∑ l, φ (m₃ l i) • s l) {x : o}
    (h : ∀ i, u₁ (u₂ (s i)) = φ x • u₃ (s i)) : m₁ * m₂ = x • m₃ := by
  ext l i
  have key := h i
  refine congrFun (uniq (fun l => (m₁ * m₂) l i) (fun l => (x • m₃) l i) ?_) l
  rw [h₂, h₃, map_sum, Finset.smul_sum] at key
  simp only [map_smul, h₁, Finset.smul_sum, smul_smul] at key
  rw [Finset.sum_comm] at key
  simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_smul, Matrix.smul_apply, smul_eq_mul]
  refine Eq.trans ?_ key
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

theorem pt_pow (ρ : S.Real) (a : S.Gam) : ρ.pt (S.r • a) ^ S.N = 1 := by
  obtain ⟨h0, hsm⟩ := pt_nsmul ρ.pt ρ.pt_add
  rw [← hsm, smul_smul, mul_comm S.N S.r, nsmul_self, h0]

theorem weil_level (hL : Laws) [hA : ArithBase o Ω] (ρ : S.Real) (a b : S.Gam) (c : (S.R)ˣ)
    (hc : (c : S.R) = algebraMap o S.R (S.ζ ^ (S.r * S.N * (S.r • eStd S.g _ a b).val))) :
    WeilIs ρ.P.A ρ.P.L S.N (ρ.pt (S.r • a)) (ρ.pt (S.r • b)) (unitOn c) := by
  have := hA.ded
  have : Algebra.FiniteType o S.R := (Subalgebra.fg_iff_finiteType _).1 S.fg
  have : IsNoetherianRing S.R := Algebra.FiniteType.isNoetherianRing o S.R
  have : IsLocallyNoetherian (Sp S.R) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of S.R)))
  let φ : o →+* Γ((baseOver (Sp S.R)).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of S.R)).inv.hom.comp (algebraMap o S.R)
  obtain ⟨h0, hsm⟩ := pt_nsmul ρ.pt ρ.pt_add
  have h₁ := ρ.weil a (S.r • b) c (by rw [eStd_nsmul, hc])
  have h₂ := (hL.weil _ ρ.P S.N (baseOver (Sp S.R))).2.2.2 S.r (ρ.pt a) (ρ.pt (S.r • b)) (unitOn c)
    (by rw [mul_comm, ← map_natCast φ]; exact S.unit.map φ)
    (by rw [← hsm, mul_comm S.N S.r, nsmul_self, h0]) (pt_pow ρ b)
  rw [hsm S.r a]
  refine h₂.1 ?_
  rw [← Nat.cast_mul, mul_comm S.N S.r]
  exact h₁

theorem rho_mul_rho (hL : Laws) [hA : ArithBase o Ω] (ρ : S.Real) (a b : S.Gam) :
    S.ρ a * S.ρ b =
      S.ζ ^ (S.r * S.N * (S.r • eStd S.g _ a b).val * ((S.N + 1) / 2)) • S.ρ (a + b) := by
  have := ρ.P.isAb.comm
  let φ : o →+* Γ((baseOver (Sp S.R)).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of S.R)).inv.hom.comp (algebraMap o S.R)
  have hφ : Function.Injective φ :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S.R)).inv).1.comp
      fun b b' h => hA.inj (congrArg Subtype.val h)
  obtain ⟨u, hu, -⟩ := GlobalTheory.thetaGrp_acts_linearly hL.globalFns _ ρ.P S.N (baseOver (Sp S.R))
  have hodd : Odd S.N := by rw [ρ.N_eq]; exact ρ.n_odd.pow.pow
  have act : ∀ a v, IsActOf ρ.P.A ρ.P.L S.N (ρ.U a) (SecM.toSec ρ.P.A v) (SecM.toSec ρ.P.A (u (ρ.U a) v)) :=
    fun a v => (hu _ _ _).2 rfl
  obtain ⟨c, hc⟩ : IsUnit (algebraMap o S.R (S.ζ ^ (S.r * S.N * (S.r • eStd S.g _ a b).val))) :=
    ((S.prim.isUnit (pow_ne_zero _ (NeZero.ne (S.r * S.N)))).pow _).map _
  have weil := weil_level hL ρ a b c hc
  have hc' : (unitOn c).val = φ (S.ζ ^ (S.r * S.N * (S.r • eStd S.g _ a b).val)) :=
    congrArg (Scheme.ΓSpecIso (CommRingCat.of S.R)).inv.hom hc
  let s : S.J → SecM ρ.P.A ρ.P.L S.N (baseOver (Sp S.R)) := fun i => SecM.ofSec ρ.P.A (ρ.s i)
  have hs : ∀ a i, u (ρ.U a) (s i) = ∑ l, φ (S.ρ a l i) • s l := fun a i =>
    (sum_iff _ s fun l => φ (S.ρ a l i)).1 (ρ.U_act a i _ (act a (s i)))
  refine matrix_mul_of_comp φ s (fun c c' h => ?_) (hs a) (hs b) (hs (a + b)) fun i => ?_
  · have := (ρ.s_basis (SecM.toSec ρ.P.A (∑ l, φ (c l) • s l))).unique
      ((sum_iff _ s fun l => φ (c l)).2 rfl) ((sum_iff _ s fun l => φ (c' l)).2 h)
    exact funext fun l => hφ (congrFun this l)
  · have := act_act hL.globalFns ρ.P.isAb ρ.P.isLB hodd (pt_pow ρ b) (ρ.U_sym a) (ρ.U_sym b)
      (by rw [← ρ.pt_add, ← smul_add, add_comm]; exact ρ.U_sym (a + b)) weil (act b (s i)) (act a _)
      (act (a + b) (s i))
    refine this.trans (congrArg (· • _) ?_)
    rw [pow_mul S.ζ (_ * _), map_pow φ, ← hc']
    exact Units.val_pow_eq_pow_val _ _

theorem exists_perp {T : AddSubgroup S.Gam} (hT : S.IsoFree T) (x : S.Gam)
    (h : ∀ t : T, S.r • eStd S.g _ t x = 0) : ∃ b : S.Gam, x - S.N • b ∈ S.perp T := by
  obtain ⟨-, d, ⟨E⟩⟩ := hT
  choose a ha using fun t : T => ZModPerp.exists_eq_nsmul_zmod (mul_comm S.N S.r) _ (h t)
  obtain ⟨b, hb⟩ := Weights.exists_eStd_eq (T.subtype.comp E.symm.toAddMonoidHom)
    (Subtype.val_injective.comp E.symm.injective) (fun i => a (E.symm (Pi.single i 1)))
  have h3 := Weights.addHom_ext_single ((Weights.eLeft S.g _ x).comp (T.subtype.comp E.symm.toAddMonoidHom))
    (S.N • (Weights.eLeft S.g _ b).comp (T.subtype.comp E.symm.toAddMonoidHom)) fun i => by
      exact (ha _).trans (congrArg (S.N • ·) (hb i).symm)
  refine ⟨b, fun t ht => ?_⟩
  have h5 : eStd S.g _ t x = S.N • eStd S.g _ t b := by
    simpa [Weights.eLeft_apply] using DFunLike.congr_fun h3 (E ⟨t, ht⟩)
  rw [← Weights.eLeft_apply, map_sub, map_nsmul, Weights.eLeft_apply, Weights.eLeft_apply, Weights.eStd_swap, h5,
    Weights.eStd_swap _ _ t b]
  simp

theorem chi_smul_rho_mul_proj {T : AddSubgroup S.Gam} (hT : S.IsoFree T) (c : T →+ ZMod S.N) (s : T) :
    chi S (c s) • (S.ρ s * S.proj T c) = S.proj T c := by
  have := Fintype.ofFinite T
  rw [proj_eq, mul_smul_comm, smul_comm, Finset.mul_sum, Finset.smul_sum,
    ← Equiv.sum_comp (Equiv.addLeft s) fun t : T => chi S (c t) • S.ρ t]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mul_smul_comm, smul_smul, ρ_mul_ρ hT, ← chi_add, ← map_add]
  rfl

theorem rho_comm (hodd : Odd S.N) (hmul : ∀ a b, S.ρ a * S.ρ b =
      S.ζ ^ (S.r * S.N * (S.r • eStd S.g _ a b).val * ((S.N + 1) / 2)) • S.ρ (a + b)) (a b : S.Gam) :
    S.ρ a * S.ρ b = (S.ζ ^ (S.r * S.N)) ^ (S.r • eStd S.g _ a b).val • (S.ρ b * S.ρ a) := by
  have hω : IsPrimitiveRoot (S.ζ ^ (S.r * S.N)) (S.r * S.N) :=
    S.prim.pow (pow_pos (NeZero.pos _) 2) (sq _)
  rw [hmul, hmul b a, add_comm b a, smul_smul, _root_.mul_assoc, _root_.mul_assoc (S.r * S.N), pow_mul S.ζ (S.r * S.N),
    pow_mul S.ζ (S.r * S.N) (_ * _), ← pow_add]
  congr 1
  rw [pow_eq_pow_mod _ hω.pow_eq_one, pow_eq_pow_mod (_ + _) hω.pow_eq_one]
  congr 1
  refine (ZMod.natCast_eq_natCast_iff' _ _ _).1 ?_
  obtain ⟨m, hm⟩ := hodd
  have h1 : (S.N + 1) / 2 = m + 1 := by omega
  have h2 : ((S.r : ZMod (S.r * S.N)) * (2 * m + 1)) = 0 := by
    have := ZMod.natCast_self (S.r * S.N)
    rw [Nat.cast_mul] at this
    rw [← this]
    congr 1
    exact_mod_cast congrArg (Nat.cast : ℕ → ZMod (S.r * S.N)) hm.symm
  rw [h1, Weights.eStd_swap _ _ a b]
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val, nsmul_eq_mul, Nat.cast_one]
  linear_combination (eStd S.g _ a b) * h2

theorem irred_of_comm [IsDomain o] (hc : Fintype.card S.J = S.N ^ S.g)
    (hcomm : ∀ a b, S.ρ a * S.ρ b = (S.ζ ^ (S.r * S.N)) ^ (S.r • eStd S.g _ a b).val • (S.ρ b * S.ρ a))
    {F : Type} [Field F] (y : o →+* F) {T : AddSubgroup S.Gam} (hT : S.IsoFree T) (c : T →+ ZMod S.N)
    (W : Submodule F (S.J → F)) (hW : ∀ v ∈ W, ((S.proj T c).map y).mulVec v = v)
    (hst : ∀ h ∈ S.perp T, ∀ v ∈ W, ((S.ρ h).map y).mulVec v ∈ W) :
    W = ⊥ ∨ ∀ v, ((S.proj T c).map y).mulVec v = v → v ∈ W := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨u, huW, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  let Λ : Matrix S.J S.J o →+* Module.End F (S.J → F) :=
    (Matrix.toLinAlgEquiv' (R := F) (n := S.J)).toRingEquiv.toRingHom.comp y.mapMatrix
  have hΛ : ∀ M v, Λ M v = (M.map y).mulVec v := fun M v => Matrix.toLinAlgEquiv'_apply _ _
  have hΛs : ∀ (x : o) M, Λ (x • M) = y x • Λ M := fun x M => LinearMap.ext fun v => by
    rw [LinearMap.smul_apply, hΛ, hΛ, ← Matrix.smul_mulVec]
    congr 1
    ext i j
    simp
  simp only [← hΛ] at hW hst ⊢
  have hω : IsPrimitiveRoot (y (S.ζ ^ (S.r * S.N))) (S.r * S.N) := by
    have hω : IsPrimitiveRoot (S.ζ ^ (S.r * S.N)) (S.r * S.N) :=
      S.prim.pow (pow_pos (NeZero.pos _) 2) (sq _)
    have : NeZero ((S.r * S.N : ℕ) : F) := ⟨by simpa only [map_natCast] using (S.unit.map y).ne_zero⟩
    rw [← Polynomial.isRoot_cyclotomic_iff, ← Polynomial.map_cyclotomic _ y]
    exact (hω.isRoot_cyclotomic (NeZero.pos _)).map
  have hζ : y S.ζ ≠ 0 := ((S.prim.isUnit (pow_ne_zero _ (NeZero.ne (S.r * S.N)))).map y).ne_zero
  let ψ : ZMod (S.r * S.N) → F := fun x => y (S.ζ ^ (S.r * S.N)) ^ x.val
  have ψinj : Function.Injective ψ := fun x x' h =>
    ZMod.val_injective _ (hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h)
  have ψadd : ∀ x x', ψ (x + x') = ψ x * ψ x' := fun x x' => by
    simp only [ψ]
    rw [ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ hω.pow_eq_one).symm
  have ψ0 : ψ 0 = 1 := by simp [ψ]
  have comm : ∀ a b v, Λ (S.ρ a) (Λ (S.ρ b) v) = ψ (S.r • eStd S.g _ a b) • Λ (S.ρ b) (Λ (S.ρ a) v) :=
    fun a b v => by
      have := LinearMap.congr_fun (congrArg Λ (hcomm a b)) v
      rwa [hΛs, map_mul, map_mul, map_pow] at this
  have mul : ∀ a b, ∃ k : F, k ≠ 0 ∧ ∀ v, Λ (S.ρ a) (Λ (S.ρ b) v) = k • Λ (S.ρ (a + b)) v := fun a b => by
    obtain ⟨k, hk⟩ := S.ρ_mul a b
    refine ⟨y S.ζ ^ k, pow_ne_zero _ hζ, fun v => ?_⟩
    have := LinearMap.congr_fun (congrArg Λ hk) v
    rwa [hΛs, map_mul, map_pow] at this
  have inj : ∀ a, Function.Injective (Λ (S.ρ a)) := fun a v v' h => by
    obtain ⟨k, hk, h'⟩ := mul (-a) a
    rw [neg_add_cancel, S.ρ_one 0 (smul_zero _), map_one] at h'
    exact smul_right_injective _ hk ((h' v).symm.trans ((congrArg _ h).trans (h' v')))

  let σ : (Fin S.g ⊕ Fin S.g → ZMod S.N) → S.Gam := fun a i => ((a i).val : ZMod (S.r * S.N))
  have hli : LinearIndependent F fun a => Λ (S.ρ (σ a)) := by
    refine linearIndependent_of_comm_smul _ (fun a b => ψ (S.r • eStd S.g _ (σ a) (σ b))) (fun a => inj _)
      (fun a b v => comm _ _ v) fun a a' h => funext fun i => ?_
    have h1 : (1 : ZMod S.N).val = 1 := by
      have : Fact (1 < S.N) := ⟨S.N_ge⟩
      exact ZMod.val_one _
    have h2 : ∀ j, σ (Pi.single j 1) = Pi.single j 1 := fun j => funext fun l => by
      by_cases hl : l = j
      · subst hl; simp only [σ, Pi.single_eq_same, h1, Nat.cast_one]
      · simp [σ, hl]
    have h3 : S.r • σ a i = S.r • σ a' i := by
      rcases i with i | i
      · have := ψinj (congrFun h (Pi.single (.inr i) 1))
        rw [h2] at this
        simpa [eStd, Pi.single_apply] using this
      · have := ψinj (congrFun h (Pi.single (.inl i) 1))
        rw [h2] at this
        simpa [eStd, Pi.single_apply] using this
    simp only [σ, nsmul_eq_mul, ← Nat.cast_mul] at h3
    have h4 := Nat.ModEq.mul_left_cancel' (by have := S.r_pos; omega) ((ZMod.natCast_eq_natCast_iff _ _ _).1 h3)
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h4
    exact h4
  have hspan : Submodule.span F (Set.range fun a => Λ (S.ρ (σ a))) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank'
    rw [Module.finrank_linearMap, Module.finrank_fintype_fun_eq_card, hc, ← pow_add]
    simp

  have := Fintype.ofFinite T
  have hu : ∀ t : T, y (chi S (c t)) • Λ (S.ρ t) u = u := fun t => by
    have := LinearMap.congr_fun (congrArg Λ (chi_smul_rho_mul_proj hT c t)) u
    rwa [hΛs, map_mul, LinearMap.smul_apply, Module.End.mul_apply, hW u huW] at this
  have hP : ∀ a, Λ (S.proj T c) (Λ (S.ρ a) u) ∈ W := fun a => by
    have e : Λ (S.proj T c) (Λ (S.ρ a) u) = y (Ring.inverse (Nat.card T : o)) •
        (∑ t : T, ψ (S.r • eStd S.g _ t a)) • Λ (S.ρ a) u := by
      rw [proj_eq, hΛs, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, Finset.sum_smul]
      congr 1
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [hΛs, LinearMap.smul_apply, comm, smul_comm, ← map_smul, hu]
    rw [e]
    refine W.smul_mem _ ?_
    by_cases h : ∀ t : T, S.r • eStd S.g _ t a = 0
    · obtain ⟨b, hb⟩ := exists_perp hT a h
      obtain ⟨k, hk, h'⟩ := mul (a - S.N • b) (S.N • b)
      rw [sub_add_cancel, S.ρ_one (S.N • b) (by rw [smul_smul, nsmul_self]), map_one] at h'
      refine W.smul_mem _ ((W.smul_mem_iff hk).1 ?_)
      rw [← h']
      exact hst _ hb u huW
    · obtain ⟨t, ht⟩ := not_forall.1 h
      rw [sum_eq_zero_of_mul (fun t : T => ψ (S.r • eStd S.g _ t a)) (a := t) (fun s t => ?_)
        (fun h => ht (ψinj (h.trans ψ0.symm))), zero_smul]
      · exact W.zero_mem
      · rw [← ψadd, ← smul_add]
        exact congrArg (fun x => ψ (S.r • x)) ((Weights.eLeft S.g _ a).map_add s t)
  intro v hv
  obtain ⟨f, hf⟩ : ∃ f : (S.J → F) →ₗ[F] (S.J → F), f u = v := by
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F hu0
    exact ⟨φ.smulRight v, by simp [hφ]⟩
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp
    (hspan ▸ Submodule.mem_top : f ∈ Submodule.span F (Set.range fun a => Λ (S.ρ (σ a))))
  rw [← hv, ← hf, ← hd, LinearMap.sum_apply, map_sum]
  refine W.sum_mem fun a _ => ?_
  rw [LinearMap.smul_apply, map_smul]
  exact W.smul_mem _ (hP _)

end GlobalTheory.WeightIrred

namespace GlobalTheory

open WeightIrred in

theorem weightSpace_irreducible_residue : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y : o →+* OO p) (T : AddSubgroup S.Gam), S.IsoFree T → ∀ (c : T →+ ZMod S.N) (W : Submodule (kb p) (S.J → kb p)), (∀ v ∈ W, ((S.proj T c).map fun a => IsLocalRing.residue (OO p) (y a)).mulVec v = v) → (∀ h ∈ S.perp T, ∀ v ∈ W, ((S.ρ h).map fun a => IsLocalRing.residue (OO p) (y a)).mulVec v ∈ W) → W = ⊥ ∨ ∀ v, ((S.proj T c).map fun a => IsLocalRing.residue (OO p) (y a)).mulVec v = v → v ∈ W := by
  intro hL o Ω _ _ _ hA S ρ p _ y T hT c W hW hst
  have : IsDomain o := hA.inj.isDomain _
  exact irred_of_comm ρ.card
    (rho_comm (by rw [ρ.N_eq]; exact ρ.n_odd.pow.pow) (rho_mul_rho hL.1 ρ))
    ((IsLocalRing.residue (OO p)).comp y) hT c W hW hst

end GlobalTheory
