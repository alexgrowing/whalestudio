import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistModuleFreeAndGeneratorSummand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnityStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

set_option maxHeartbeats 1000000
noncomputable section

namespace GlobalTheory.TwSec

abbrev twP (q : ℕ) (i : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) := Scheme.Γ ⋙ twF q i

abbrev fsec (q : ℕ) (i : ℤ) {U : Scheme.{0}} (f : Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) : Sec (tw q i) U :=
  ofRings.sec (twF q i) U (Submodule.Quotient.mk f)

theorem ulift_smul {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] (r : ZMod q) (m : M) :
    (ULift.up r : ULift.{1} (ZMod q)) • m = r.val • m := by
  have h : (ULift.up r : ULift.{1} (ZMod q)) = ((r.val : ℕ) : ULift.{1} (ZMod q)) := by
    ext; rw [ULift.down_natCast, ZMod.natCast_zmod_val]
  rw [h, Nat.cast_smul_eq_nsmul]

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res (k ≫ g) y = Sec.res k (Sec.res g y) := by
  simp [Sec.res]

theorem prim_map_comp {q : ℕ} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    (ζ.map g.appTop.hom).map k.appTop.hom = ζ.map (k ≫ g).appTop.hom := by
  rw [Scheme.Hom.comp_appTop]; rfl

theorem res_fsec {q : ℕ} {i : ℤ} {V U : Scheme.{0}} (g : V ⟶ U) (f : Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) :
    Sec.res g (fsec q i f) = fsec q i (Finsupp.mapDomain (Prim.map g.appTop.hom) f) := by
  have h := congrArg (fun φ => φ.hom (Submodule.Quotient.mk (p := twRel q i Γ(U, ⊤)) f))
    ((toSheafify Scheme.etaleTopology (twP q i)).naturality g.op)
  exact h.symm

theorem res_twGen {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
  have := res_fsec (i := i) g (Finsupp.single ζ 1)
  rw [Finsupp.mapDomain_single] at this
  exact this

theorem fsec_single {q : ℕ} [NeZero q] (i : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (b : ULift.{1} (ZMod q)) :
    fsec q i (Finsupp.single ζ b) = b.down.val • twGen i ζ := by
  obtain ⟨b⟩ := b
  rw [← ulift_smul, ← Finsupp.smul_single_one]
  show ofRings.sec (twF q i) U (Submodule.Quotient.mk _) = _
  rw [Submodule.Quotient.mk_smul]
  exact map_smul _ _ _

theorem twGen_rel {q : ℕ} [NeZero q] (i : ℤ) {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) : twGen i ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • twGen i ζ := by
  have hq : (Submodule.Quotient.mk (Finsupp.single ξ 1) : (Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q i Γ(U, ⊤)) =
      Submodule.Quotient.mk (Finsupp.single ζ (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q))) :=
    (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩)
  change ofRings.sec (twF q i) U _ = _
  rw [hq]
  exact fsec_single i ζ _

end GlobalTheory.TwSec

end

noncomputable section
namespace GlobalTheory.TwSec

theorem loc_all {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  GlobalTheory.EtC.loc_calculus.1 U P h

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (h : ∀ V g, P V g → Q V g) :
    Loc U Q := GlobalTheory.EtC.loc_calculus.2.1 U P Q hP h

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := GlobalTheory.EtC.loc_calculus.2.2.1 U P Q hP hQ

theorem loc_trans {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U fun V g => Loc V fun W k => P W (k ≫ g)) : Loc U P := GlobalTheory.EtC.loc_calculus.2.2.2.2.1 U P h

theorem res_add {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a + b) = Sec.res g a + Sec.res g b := map_add _ _ _

theorem res_zero {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) :
    Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (c : ℕ) (a : Sec F U) :
    Sec.res g (c • a) = c • Sec.res g a := map_nsmul _ _ _

theorem fsec_nsmul {q : ℕ} (i : ℤ) {U : Scheme.{0}} (c : ℕ) (f : Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) :
    fsec q i (c • f) = c • fsec q i f := by
  show ofRings.sec (twF q i) U (Submodule.Quotient.mk _) = _
  rw [Submodule.Quotient.mk_smul]
  exact map_nsmul _ _ _

theorem fsec_zero {q : ℕ} (i : ℤ) {U : Scheme.{0}} : fsec q i (0 : Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) = 0 := by
  show ofRings.sec (twF q i) U (Submodule.Quotient.mk _) = _
  rw [Submodule.Quotient.mk_zero]
  exact map_zero _

theorem fsec_add {q : ℕ} (i : ℤ) {U : Scheme.{0}} (f₁ f₂ : Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) :
    fsec q i (f₁ + f₂) = fsec q i f₁ + fsec q i f₂ := by
  show ofRings.sec (twF q i) U (Submodule.Quotient.mk _) = _
  rw [Submodule.Quotient.mk_add]
  exact map_add _ _ _

theorem fsec_loc_mult {q : ℕ} [NeZero q] (i : ℤ) {V : Scheme.{0}} (ζ : Prim q Γ(V, ⊤))
    (f : Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) :
    Loc V fun W k => ∃ c : ℕ, Sec.res k (fsec q i f) = c • twGen i (ζ.map k.appTop.hom) := by
  induction f using Finsupp.induction_linear with
  | zero => exact loc_all fun W k => ⟨0, by rw [fsec_zero, res_zero, zero_smul]⟩
  | add f₁ f₂ h₁ h₂ =>
    refine loc_mono (loc_and h₁ h₂) fun W k h => ?_
    obtain ⟨⟨c₁, e₁⟩, ⟨c₂, e₂⟩⟩ := h
    exact ⟨c₁ + c₂, by rw [fsec_add, res_add, e₁, e₂, add_smul]⟩
  | single ξ b =>
    refine loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.1 ζ ξ) fun W k h => ?_
    obtain ⟨a, ha⟩ := h
    refine ⟨b.down.val * ((a ^ i : (ZMod q)ˣ) : ZMod q).val, ?_⟩
    rw [fsec_single, res_nsmul, res_twGen, twGen_rel i (ζ.map k.appTop.hom) (ξ.map k.appTop.hom) a ha, smul_smul]

theorem loc_mult {q : ℕ} [NeZero q] (i : ℤ) (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U) :
    Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom) := by
  refine loc_trans (loc_mono ((GlobalTheory.EtC.toSheafify_loc_bij_lift (ZMod q) (twP q i)).1 U y) ?_)
  rintro V g ⟨x, hx⟩
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hx' : fsec q i f = Sec.res g y := hx
  refine loc_mono (fsec_loc_mult i (ζ.map g.appTop.hom) f) fun W k h => ?_
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  rw [res_comp, ← hx', ← prim_map_comp]
  exact hc

theorem loc_gen {q : ℕ} [NeZero q] (i : ℤ) (U : Scheme.{0}) (y : Sec (tw q i) U) :
    Loc U fun V g => Sec.res g y = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g y = c • twGen i ζ := by
  refine loc_trans (loc_mono ((GlobalTheory.EtC.toSheafify_loc_bij_lift (ZMod q) (twP q i)).1 U y) ?_)
  rintro V g ⟨x, hx⟩
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hx' : fsec q i f = Sec.res g y := hx
  rcases isEmpty_or_nonempty (Prim q Γ(V, ⊤)) with hP | hne
  · refine loc_all fun W k => Or.inl ?_
    have hf : f = 0 := Finsupp.ext fun ζ => (hP.false ζ).elim
    rw [res_comp, ← hx', hf]
    show Sec.res k (fsec q i (0 : Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q))) = 0
    rw [fsec_zero, res_zero]
  · obtain ⟨ζ⟩ := hne
    refine loc_mono (fsec_loc_mult i ζ f) fun W k h => ?_
    obtain ⟨c, hc⟩ := h
    refine Or.inr ⟨ζ.map k.appTop.hom, c, ?_⟩
    rw [res_comp, ← hx']
    exact hc

theorem dvd_of_smul_eq_zero {q : ℕ} [NeZero q] (i : ℤ) (U : Scheme.{0}) [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c : ℕ)
    (h : c • twGen i ζ = 0) : q ∣ c := by
  have h0 : fsec q i (c • Finsupp.single ζ 1) = 0 := by
    rw [fsec_nsmul]
    exact h
  have hl := (GlobalTheory.EtC.toSheafify_loc_bij_lift (ZMod q) (twP q i)).2.1 U _ h0
  rw [GlobalTheory.EtC.loc_iff_etale_affine_points] at hl
  · obtain ⟨x⟩ := ‹Nonempty U›
    obtain ⟨V, g, -, -, ⟨v, -⟩, hg⟩ := hl x
    haveI : Nontrivial Γ(V, ⊤) := @Scheme.component_nontrivial V ⊤ ⟨⟨v, trivial⟩⟩
    obtain ⟨φ, hφ⟩ := (GlobalTheory.TwFree.twist_free q i Γ(V, ⊤)).2 (ζ.map g.appTop.hom)
    have hg' : c • (Submodule.Quotient.mk (Finsupp.single (ζ.map g.appTop.hom) 1) :
        (Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q i Γ(V, ⊤)) = 0 := by
      refine Eq.trans ?_ hg
      show _ = Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.appTop.hom) (c • Finsupp.single ζ 1))
      rw [Finsupp.mapDomain_smul, Finsupp.mapDomain_single, Submodule.Quotient.mk_smul]
    have h1 := congrArg φ hg'
    rw [map_nsmul, hφ, map_zero] at h1
    have h2 := congrArg ULift.down h1
    rw [← ZMod.natCast_eq_zero_iff]
    simpa using h2
  · intro V W g k hk
    have h3 := congrArg ((twP q i).map k.op).hom hk
    rw [map_zero] at h3
    refine Eq.trans ?_ h3
    rw [op_comp, Functor.map_comp]
    rfl

end GlobalTheory.TwSec
end

noncomputable section
namespace GlobalTheory.TwSec

def liftU {q : ℕ} [NeZero q] (i : ℤ) (M : Shv (ZMod q)) (U : Scheme.{0}) (e : Prim q Γ(U, ⊤) → Sec M U)
    (hr : ∀ (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val →
      e ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • e ζ) :
    ((Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q i Γ(U, ⊤)) →ₗ[ULift.{1} (ZMod q)] Sec M U :=
  (twRel q i Γ(U, ⊤)).liftQ (Finsupp.linearCombination _ e) (by
    refine Submodule.span_le.2 ?_
    rintro x ⟨ζ, ξ, a, h, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, Finsupp.linearCombination_single, one_smul]
    rw [hr ζ ξ a h, ulift_smul, sub_self])

theorem liftU_single {q : ℕ} [NeZero q] (i : ℤ) (M : Shv (ZMod q)) (U : Scheme.{0}) (e : Prim q Γ(U, ⊤) → Sec M U) hr
    (ζ : Prim q Γ(U, ⊤)) : liftU i M U e hr (Submodule.Quotient.mk (Finsupp.single ζ 1)) = e ζ := by
  show Finsupp.linearCombination _ e (Finsupp.single ζ 1) = e ζ
  rw [Finsupp.linearCombination_single, one_smul]

theorem liftU_nat {q : ℕ} [NeZero q] (i : ℤ) (M : Shv (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec M U)
    (he : ∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom))
    (hr : ∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val →
      e U ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • e U ζ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    liftU i M V (e V) (hr V) (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.appTop.hom) (Finsupp.single ζ 1))) =
      Sec.res g (liftU i M U (e U) (hr U) (Submodule.Quotient.mk (Finsupp.single ζ 1))) := by
  rw [Finsupp.mapDomain_single, liftU_single, liftU_single, he]

theorem lift_unique {q : ℕ} [NeZero q] (i : ℤ) (M : Shv (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec M U)
    (he : ∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom))
    (hr : ∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val →
      e U ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • e U ζ) :
    ∃! φ : tw q i ⟶ M, ∀ U ζ, Sec.map φ (twGen i ζ) = e U ζ := by
  let ψ : twP q i ⟶ M.obj :=
    { app := fun U => ModuleCat.ofHom (liftU i M U.unop (e U.unop) (hr U.unop))
      naturality := by
        intro U V g
        ext : 1
        apply Submodule.linearMap_qext
        apply Finsupp.lhom_ext'
        intro ζ
        apply LinearMap.ext_ring
        exact liftU_nat i M e he hr g.unop ζ }
  obtain ⟨φ, hφ, huniq⟩ := (GlobalTheory.EtC.toSheafify_loc_bij_lift (ZMod q) (twP q i)).2.2 M ψ
  have key : ∀ (χ : tw q i ⟶ M) (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map χ (twGen i ζ) = ((toSheafify Scheme.etaleTopology (twP q i) ≫ χ.hom).app (op U)).hom
        (Submodule.Quotient.mk (Finsupp.single ζ 1)) := fun _ _ _ => rfl
  refine ⟨φ, fun U ζ => ?_, fun φ' hφ' => huniq φ' ?_⟩
  · refine (key φ U ζ).trans ?_
    rw [hφ]
    exact liftU_single i M U (e U) (hr U) ζ
  · ext U : 2
    apply ModuleCat.hom_ext
    apply Submodule.linearMap_qext
    apply Finsupp.lhom_ext'
    intro ζ
    apply LinearMap.ext_ring
    have h2 := (key φ' U.unop ζ).symm.trans (hφ' U.unop ζ)
    exact h2.trans (liftU_single i M U.unop (e U.unop) (hr U.unop) ζ).symm

end GlobalTheory.TwSec

namespace GlobalTheory.EtC

theorem twist_sections : ∀ (q : ℕ) [NeZero q] (i : ℤ), (∀ (U : Scheme.{0}) (y : Sec (tw q i) U), Loc U fun V g => Sec.res g y = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g y = c • twGen i ζ) ∧ (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U), Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c : ℕ), c • twGen i ζ = 0 → q ∣ c) ∧ (∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)), Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → twGen i ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • twGen i ζ) ∧ ∀ (M : Shv (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom)) → (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → e U ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • e U ζ) → ∃! φ : tw q i ⟶ M, ∀ U ζ, Sec.map φ (twGen i ζ) = e U ζ := by
  intro q _ i
  exact ⟨GlobalTheory.TwSec.loc_gen i, fun U ζ y => GlobalTheory.TwSec.loc_mult i U ζ y,
    fun U _ ζ c h => GlobalTheory.TwSec.dvd_of_smul_eq_zero i U ζ c h, fun V U g ζ => GlobalTheory.TwSec.res_twGen i g ζ,
    fun U ζ ξ a h => GlobalTheory.TwSec.twGen_rel i ζ ξ a h, fun M e he hr => GlobalTheory.TwSec.lift_unique i M e he hr⟩

end GlobalTheory.EtC
end
