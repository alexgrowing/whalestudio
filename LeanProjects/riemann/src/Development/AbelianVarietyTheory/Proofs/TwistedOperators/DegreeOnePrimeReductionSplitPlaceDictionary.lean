import Mathlib
import ReciprocityTheory.Automorphisms.PlaceA
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaceRed

section Gen

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

theorem mem_max_iff (a : v.adicCompletionIntegers F) :
    IsLocalRing.residue (v.adicCompletionIntegers F) a = 0 ↔ Valued.v (a : v.adicCompletion F) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff]
  exact Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) _))

theorem exists_red {A : Type} [CommRing A] (I : Ideal A) (ψ : A →+* v.adicCompletionIntegers F)
    (hI : ∀ x, x ∈ I ↔ Valued.v (ψ x : v.adicCompletion F) < 1)
    (hs : ∀ a : v.adicCompletionIntegers F, ∃ x, Valued.v ((a : v.adicCompletion F) - ψ x) < 1) :
    ∃ r : v.adicCompletionIntegers F →+* A ⧸ I, (∀ x, r (ψ x) = Ideal.Quotient.mk I x) ∧
      ∀ a, r a = 0 ↔ Valued.v (a : v.adicCompletion F) < 1 := by
  let q := Ideal.Quotient.lift I ((IsLocalRing.residue _).comp ψ)
    (fun x hx => (mem_max_iff _).2 ((hI x).1 hx))
  have hq : Function.Bijective q := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro y hy
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact Ideal.Quotient.eq_zero_iff_mem.2 ((hI x).2 ((mem_max_iff _).1 hy))
    · intro y
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨x, hx⟩ := hs a
      refine ⟨Ideal.Quotient.mk I x, ?_⟩
      show IsLocalRing.residue _ (ψ x) = _
      rw [eq_comm, ← sub_eq_zero, ← map_sub, mem_max_iff]
      exact hx
  let e := RingEquiv.ofBijective q hq
  refine ⟨(e.symm : _ →+* A ⧸ I).comp (IsLocalRing.residue _), fun x => ?_, fun a => ?_⟩
  · show e.symm _ = _
    rw [RingEquiv.symm_apply_eq]
    rfl
  · show e.symm _ = 0 ↔ _
    rw [map_eq_zero_iff _ e.symm.injective, mem_max_iff]

theorem exists_unitPart : ∃ t : (v.adicCompletion F)ˣ →* v.adicCompletionIntegers F,
    ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → (t u : v.adicCompletion F) = u := by
  obtain ⟨p, hp⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-1))
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  have hne : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) ≠ 0 := fun u =>
    (Valuation.ne_zero_iff _).2 u.ne_zero
  have hv : ∀ u : (v.adicCompletion F)ˣ,
      Valued.v ((u : v.adicCompletion F) * p ^ (WithZero.log (Valued.v (u : v.adicCompletion F)))) = 1 := by
    intro u
    rw [map_mul, map_zpow₀, hp, ← WithZero.exp_zsmul]
    conv_lhs => lhs; rw [← WithZero.exp_log (hne u)]
    rw [← WithZero.exp_add]
    simp
  refine ⟨⟨⟨fun u => ⟨(u : v.adicCompletion F) * p ^ (WithZero.log (Valued.v (u : v.adicCompletion F))),
    (hv u).le⟩, ?_⟩, ?_⟩, ?_⟩
  · apply Subtype.ext
    simp
  · intro a b
    apply Subtype.ext
    show ((a * b : (v.adicCompletion F)ˣ) : v.adicCompletion F) * p ^ _ = (_ * p ^ _) * (_ * p ^ _)
    rw [Units.val_mul, map_mul, WithZero.log_mul (hne a) (hne b), zpow_add₀ hp0]
    ring
  · intro u hu
    show (u : v.adicCompletion F) * p ^ _ = _
    rw [hu]
    simp

end Gen

variable {D : D7} {v : FinPl D} (φ : SplitProj D v)

def rdQh : D.host.E →+* Fv D.host.F v :=
  φ.toRingHom.comp (Algebra.TensorProduct.includeRight (R := D.host.F) (A := Fv D.host.F v) (B := D.host.E)).toRingHom

theorem rdQh_apply (x : D.host.E) : rdQh φ x = rdQ φ x := rfl

theorem rdQ_int (x : 𝓞 D.host.E) : rdQ φ (x : D.host.E) ∈ v.adicCompletionIntegers D.host.F := by
  obtain ⟨p, hm, hp⟩ : IsIntegral ℤ (x : D.host.E) := x.2
  refine ReciprocityTheory.Aut.adic_le_one_of_poly v p hm ?_
  have := congrArg (rdQh φ) hp
  rw [Polynomial.hom_eval₂, map_zero, RingHom.ext_int ((rdQh φ).comp _) (Int.castRingHom _)] at this
  exact this

theorem rdQ_alg (y : D.host.F) :
    rdQ φ (algebraMap D.host.F D.host.E y) = algebraMap D.host.F (Fv D.host.F v) y := by
  show φ ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Fv D.host.F v) (B := D.host.E))
    (algebraMap D.host.F D.host.E y)) = _
  rw [AlgHom.commutes]
  exact φ.commutes (algebraMap D.host.F (Fv D.host.F v) y)

def rdO : 𝓞 D.host.E →+* v.adicCompletionIntegers D.host.F :=
  ((rdQh φ).comp (algebraMap (𝓞 D.host.E) D.host.E)).codRestrict (v.adicCompletionIntegers D.host.F) (rdQ_int φ)

theorem rdO_coe (x : 𝓞 D.host.E) : (rdO φ x : Fv D.host.F v) = rdQ φ (x : D.host.E) := rfl

theorem rdO_dense (a : v.adicCompletionIntegers D.host.F) :
    ∃ x, Valued.v ((a : Fv D.host.F v) - rdO φ x) < 1 := by
  obtain ⟨y, hy⟩ := ReciprocityTheory.Aut.adic_exists_approx v (a : Fv D.host.F v) a.2
  refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y, ?_⟩
  have h1 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.F D.host.E (algebraMap (𝓞 D.host.F) D.host.F y) := by
    show algebraMap (𝓞 D.host.E) D.host.E _ = _
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [rdO_coe, h1, rdQ_alg]
  exact hy

theorem rdE_tmul (x : D.host.E) (y : Af D.host.F) :
    rdE φ (x ⊗ₜ[D.host.F] y) = φ (y v ⊗ₜ[D.host.F] x) := rfl

theorem rdE_int (N : EAf D) (hN : N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    rdE φ N ∈ v.adicCompletionIntegers D.host.F := by
  have hle : Formalism.L2.Herm.intAf D.host.F D.host.E ≤
      (v.adicCompletionIntegers D.host.F).toSubring.comap (rdE φ) := by
    refine Subring.closure_le.2 ?_
    rintro x (⟨b, rfl⟩ | ⟨y, rfl⟩)
    · obtain ⟨b0, hb0⟩ := b.2
      show rdE φ ((b : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) ∈ v.adicCompletionIntegers D.host.F
      rw [← hb0]
      exact rdQ_int φ b0
    · show rdE φ ((1 : D.host.E) ⊗ₜ[D.host.F] (y : Af D.host.F)) ∈ v.adicCompletionIntegers D.host.F
      rw [rdE_tmul]
      have : φ ((y : Af D.host.F) v ⊗ₜ[D.host.F] (1 : D.host.E)) = (y : Af D.host.F) v := φ.commutes _
      rw [this]
      exact y.2 v
  exact hle hN

def rdS : Formalism.L2.Herm.intAf D.host.F D.host.E →+* v.adicCompletionIntegers D.host.F :=
  ((rdE φ).comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype).codRestrict (v.adicCompletionIntegers D.host.F)
    (fun N => rdE_int φ N.1 N.2)

theorem rdS_oToS (x : 𝓞 D.host.E) : rdS φ (Formalism.L2.DIV.oToS D.host.F D.host.E x) = rdO φ x := rfl

theorem eq_resS {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (PP : Formalism.L2.DIV.Pl E) (g : Formalism.L2.Herm.intAf F E →+* Formalism.L2.DIV.kP PP)
    (hg : ∀ x, g (Formalism.L2.DIV.oToS F E x) = Ideal.Quotient.mk PP.asIdeal x) (N : Formalism.L2.Herm.intAf F E) :
    g N = Formalism.L2.DIV.resS F PP N := by
  have key : ∀ g' : Formalism.L2.Herm.intAf F E →+* Formalism.L2.DIV.kP PP,
      (∀ x, g' (Formalism.L2.DIV.oToS F E x) = Ideal.Quotient.mk PP.asIdeal x) →
      Formalism.L2.DIV.idS F PP.asIdeal ≤ RingHom.ker g' := by
    intro g' hg'
    refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, hg']
    exact Ideal.Quotient.eq_zero_iff_mem.2 hx
  obtain ⟨q, hq⟩ := Formalism.L2.DIV.cmpS_surj (F := F) PP.asIdeal PP.ne_bot (Ideal.Quotient.mk _ N)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hm : Formalism.L2.DIV.oToS F E b - N ∈ Formalism.L2.DIV.idS F PP.asIdeal := Ideal.Quotient.eq.1 hq
  have h1 := key g hg hm
  have h2 := key _ (Formalism.L2.DIV.resS_oToS (F := F) PP) hm
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h1 h2
  rw [← h1, ← h2, hg, Formalism.L2.DIV.resS_oToS]

theorem red_dict : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E), IsProjAt φ PP → (∃ r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP, Function.Surjective r ∧ (∀ a : v.adicCompletionIntegers D.host.F, r a = 0 ↔ Valued.v (a : Fv D.host.F v) < 1) ∧ (∀ (a : Fv D.host.F v) (b : Formalism.L2.DIV.kP PP), RedRel φ PP a b ↔ ∃ h : a ∈ v.adicCompletionIntegers D.host.F, r ⟨a, h⟩ = b) ∧ ∀ (N : EAf D) (hN : N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), ∃ h : rdE φ N ∈ v.adicCompletionIntegers D.host.F, r ⟨rdE φ N, h⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨N, hN⟩) ∧ ∀ ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ, ∃ mu : (Fv D.host.F v)ˣ →* ℂˣ, LiftsChar φ PP mu ξ := by
  intro D v φ PP hP
  obtain ⟨r, hr, hr0⟩ := exists_red PP.asIdeal (rdO φ) hP (rdO_dense φ)
  have hrel : ∀ (a : Fv D.host.F v) (b : Formalism.L2.DIV.kP PP),
      RedRel φ PP a b ↔ ∃ h : a ∈ v.adicCompletionIntegers D.host.F, r ⟨a, h⟩ = b := by
    intro a b
    constructor
    · rintro ⟨x, rfl, hx⟩
      have ha : a ∈ v.adicCompletionIntegers D.host.F := by
        have e : a = (a - rdQ φ (x : D.host.E)) + rdQ φ (x : D.host.E) := by ring
        rw [e]
        exact add_mem ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx.le) (rdQ_int φ x)
      refine ⟨ha, ?_⟩
      rw [← hr, ← sub_eq_zero, ← map_sub, hr0]
      exact hx
    · rintro ⟨h, rfl⟩
      obtain ⟨x, hx⟩ := rdO_dense φ ⟨a, h⟩
      refine ⟨x, ?_, hx⟩
      rw [← hr, eq_comm, ← sub_eq_zero, ← map_sub, hr0]
      exact hx
  refine ⟨⟨r, fun b => ?_, hr0, hrel, fun N hN => ⟨rdE_int φ N hN, ?_⟩⟩, fun ξ => ?_⟩
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨_, hr x⟩
  · exact eq_resS PP (r.comp (rdS φ)) (fun x => hr x) ⟨N, hN⟩
  · obtain ⟨t, ht⟩ := exists_unitPart (F := D.host.F) (v := v)
    refine ⟨ξ.comp (r.toMonoidHom.comp t).toHomUnits, fun u k huk => ?_⟩
    obtain ⟨h, hk⟩ := (hrel _ _).1 huk
    have hu : Valued.v (u : Fv D.host.F v) = 1 := by
      refine le_antisymm h (not_lt.1 fun hlt => ?_)
      have h0 : (k : Formalism.L2.DIV.kP PP) = 0 := hk ▸ (hr0 ⟨_, h⟩).2 hlt
      have : Nontrivial (Formalism.L2.DIV.kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
      exact k.ne_zero h0
    show ξ _ = ξ k
    congr 1
    apply Units.ext
    show r (t u) = k
    rw [← hk]
    congr 1
    exact Subtype.ext (ht u hu)

end GlobalTheory.PlaceRed

end
