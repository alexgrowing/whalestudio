import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistModuleFreeAndGeneratorSummandStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.Cb.TwSec

private theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (y : Sec F U) : Sec.res (k ≫ g) y = Sec.res k (Sec.res g y) := by
  simp [Sec.res]

private noncomputable def gsec {q : ℕ} (i : ℤ) (U : Scheme.{0}) :
    (Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] Sec (tw q i) U :=
  ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op U)).hom ∘ₗ (twRel q i Γ(U, ⊤)).mkQ

private theorem gsec_one {q : ℕ} (i : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) :
    gsec i U (Finsupp.single ζ 1) = twGen i ζ := rfl

end UpperTheory.Cb.TwSec

private theorem twRel_mk_single_eq_zpow_smul_mk_single_of_eq_pow {q : ℕ} (i : ℤ) {A : Type} [CommRing A] (ζ ξ : Prim q A) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    (Submodule.Quotient.mk (Finsupp.single ξ 1) : (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) =
      (ULift.up (((a ^ i : (ZMod q)ˣ) : ZMod q)) : ULift.{1} (ZMod q)) • Submodule.Quotient.mk (Finsupp.single ζ 1) := by
  rw [← Submodule.Quotient.mk_smul, Finsupp.smul_single_one, Submodule.Quotient.eq]
  exact Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩

private theorem ulift_zmod_smul_eq_val_nsmul {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (s : ULift.{1} (ZMod q)) (x : M) : s • x = s.down.val • x := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  congr 1
  apply ULift.ext
  rw [ULift.down_natCast, ZMod.natCast_zmod_val]

private theorem exists_twRel_mk_eq_nsmul_mk_single_of_support_pow {q : ℕ} [NeZero q] (i : ℤ) {A : Type} [CommRing A] (ζ : Prim q A)
    (f : Prim q A →₀ ULift.{1} (ZMod q)) (hf : ∀ ξ ∈ f.support, ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    ∃ c : ℕ, (Submodule.Quotient.mk f : (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) =
      c • Submodule.Quotient.mk (Finsupp.single ζ 1) := by
  have key : ∀ ξ, ∃ c : ℕ, (Submodule.Quotient.mk (Finsupp.single ξ (f ξ)) :
      (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) = c • Submodule.Quotient.mk (Finsupp.single ζ 1) := by
    intro ξ
    by_cases hξ : f ξ = 0
    · refine ⟨0, ?_⟩
      rw [hξ, Finsupp.single_zero, zero_smul]
      exact Submodule.Quotient.mk_zero _
    · obtain ⟨a, ha⟩ := hf ξ (Finsupp.mem_support_iff.mpr hξ)
      refine ⟨(f ξ * ULift.up (((a ^ i : (ZMod q)ˣ) : ZMod q))).down.val, ?_⟩
      rw [← ulift_zmod_smul_eq_val_nsmul, mul_smul, ← twRel_mk_single_eq_zpow_smul_mk_single_of_eq_pow i ζ ξ a ha, ← Submodule.Quotient.mk_smul, Finsupp.smul_single_one]
  choose c hc using key
  refine ⟨∑ ξ ∈ f.support, c ξ, ?_⟩
  conv_lhs => rw [← Finsupp.sum_single f]
  rw [Finsupp.sum, Finset.sum_smul, ← Finset.sum_congr rfl (fun ξ _ => hc ξ)]
  exact map_sum (twRel q i A).mkQ _ _

private theorem sec_res_gsec_eq_gsec_mapDomain {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (f : Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) :
    Sec.res g (UpperTheory.Cb.TwSec.gsec i U f) = UpperTheory.Cb.TwSec.gsec i V (Finsupp.mapDomain (Prim.map g.appTop.hom) f) := by
  have h := congrArg (fun φ => φ.hom (Submodule.Quotient.mk f : (Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q i Γ(U, ⊤)))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
  exact h.symm

private theorem gsec_single_eq_zpow_smul_gsec_single_of_eq_pow {q : ℕ} (i : ℤ) {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    UpperTheory.Cb.TwSec.gsec i U (Finsupp.single ξ 1) =
      (ULift.up (((a ^ i : (ZMod q)ˣ) : ZMod q)) : ULift.{1} (ZMod q)) • UpperTheory.Cb.TwSec.gsec i U (Finsupp.single ζ 1) := by
  rw [← map_smul]
  have e : (twRel q i Γ(U, ⊤)).mkQ (Finsupp.single ξ 1) =
      (twRel q i Γ(U, ⊤)).mkQ ((ULift.up (((a ^ i : (ZMod q)ˣ) : ZMod q)) : ULift.{1} (ZMod q)) • Finsupp.single ζ 1) := by
    rw [map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply]
    exact twRel_mk_single_eq_zpow_smul_mk_single_of_eq_pow i ζ ξ a h
  exact congrArg (fun t => ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op U)).hom t) e

private theorem exists_gsec_eq_nsmul_twGen_of_support_pow {q : ℕ} [NeZero q] (i : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤))
    (f : Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) (hf : ∀ ξ ∈ f.support, ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    ∃ c : ℕ, UpperTheory.Cb.TwSec.gsec i U f = c • twGen i ζ := by
  obtain ⟨c, hc⟩ := exists_twRel_mk_eq_nsmul_mk_single_of_support_pow i ζ f hf
  refine ⟨c, ?_⟩
  rw [← UpperTheory.Cb.TwSec.gsec_one, ← map_nsmul]
  have e : (twRel q i Γ(U, ⊤)).mkQ f = (twRel q i Γ(U, ⊤)).mkQ (c • Finsupp.single ζ 1) := by
    rw [map_nsmul]
    exact hc
  exact congrArg (fun t => ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op U)).hom t) e

theorem UpperTheory.Cb.tateTwist_sections_locally_generated :
    ∀ (q : ℕ) [NeZero q] (i : ℤ), (∀ (U : Scheme.{0}) (y : Sec (tw q i) U), Loc U fun V g => Sec.res g y = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g y = c • twGen i ζ) ∧ (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U), Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c : ℕ), c • twGen i ζ = 0 → q ∣ c) ∧ (∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)), Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → twGen i ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • twGen i ζ) ∧ ∀ (M : Shv (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom)) → (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → e U ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • e U ζ) → ∃! φ : tw q i ⟶ M, ∀ U ζ, Sec.map φ (twGen i ζ) = e U ζ := by
  intro q _ i
  have h4 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)),
      Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
    intro V U g ζ
    rw [← UpperTheory.Cb.TwSec.gsec_one, ← UpperTheory.Cb.TwSec.gsec_one, sec_res_gsec_eq_gsec_mapDomain, Finsupp.mapDomain_single]
  have h5 : ∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val →
      twGen i ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • twGen i ζ := by
    intro U ζ ξ a h
    rw [← UpperTheory.Cb.TwSec.gsec_one, ← UpperTheory.Cb.TwSec.gsec_one, gsec_single_eq_zpow_smul_gsec_single_of_eq_pow i ζ ξ a h, ulift_zmod_smul_eq_val_nsmul]
  have L := GlobalTheory.T.etaleLocal_property_calculus_rules
  have S := GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift (ZMod q) (Scheme.Γ ⋙ twF q i)
  have h2 : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U),
      Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom) := by
    classical
    intro U ζ y
    apply L.2.2.2.2.1
    refine L.2.1 U _ _ (S.1 U y) ?_
    rintro V g ⟨x, hx⟩
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' : Sec.res g y = UpperTheory.Cb.TwSec.gsec i V f := hx.symm
    have hl := L.2.2.2.2.2.1 V (↥f.support) _ (fun ξ => (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.1 (ζ.map g.appTop.hom) ξ.1)
    refine L.2.1 V _ _ hl ?_
    intro W k hk
    obtain ⟨c, hc⟩ := exists_gsec_eq_nsmul_twGen_of_support_pow i ((ζ.map g.appTop.hom).map k.appTop.hom)
      (Finsupp.mapDomain (Prim.map k.appTop.hom) f) (by
        intro ξ' hξ'
        obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hξ')
        obtain ⟨a, ha⟩ := hk ⟨ξ, hξ⟩
        exact ⟨a, ha⟩)
    refine ⟨c, ?_⟩
    have e : twGen i ((ζ.map g.appTop.hom).map k.appTop.hom) = twGen i (ζ.map (k ≫ g).appTop.hom) := by
      calc twGen i ((ζ.map g.appTop.hom).map k.appTop.hom) = Sec.res k (Sec.res g (twGen i ζ)) := by
            rw [h4, h4]
        _ = twGen i (ζ.map (k ≫ g).appTop.hom) := by
            rw [← UpperTheory.Cb.TwSec.res_comp, h4]
    rw [e] at hc
    rw [UpperTheory.Cb.TwSec.res_comp, hx']
    exact (sec_res_gsec_eq_gsec_mapDomain i k f).trans hc
  have h1 : ∀ (U : Scheme.{0}) (y : Sec (tw q i) U),
      Loc U fun V g => Sec.res g y = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g y = c • twGen i ζ := by
    intro U y
    apply L.2.2.2.2.1
    refine L.2.1 U _ _ (S.1 U y) ?_
    rintro V g ⟨x, hx⟩
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' : Sec.res g y = UpperTheory.Cb.TwSec.gsec i V f := hx.symm
    by_cases hP : Nonempty (Prim q Γ(V, ⊤))
    · obtain ⟨ζ⟩ := hP
      refine L.2.1 V _ _ (h2 V ζ (Sec.res g y)) ?_
      rintro W k ⟨c, hc⟩
      exact Or.inr ⟨_, c, by rw [UpperTheory.Cb.TwSec.res_comp]; exact hc⟩
    · apply L.1
      intro W k
      left
      have hf : f = 0 := by
        ext ξ
        exact (hP ⟨ξ⟩).elim
      rw [UpperTheory.Cb.TwSec.res_comp, hx', hf]
      exact (congrArg (Sec.res k) (map_zero (UpperTheory.Cb.TwSec.gsec i V))).trans (map_zero ((tw q i).obj.map k.op).hom)
  have h3 : ∀ (U : Scheme.{0}) [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c : ℕ), c • twGen i ζ = 0 → q ∣ c := by
    intro U _ ζ c h
    have hz : UpperTheory.Cb.TwSec.gsec i U (c • Finsupp.single ζ 1) = 0 := by
      rw [map_nsmul, UpperTheory.Cb.TwSec.gsec_one]
      exact h
    have hl := S.2.1 U ((twRel q i Γ(U, ⊤)).mkQ (c • Finsupp.single ζ 1)) hz
    obtain ⟨u⟩ := ‹Nonempty U›
    have hmono : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V),
        ((Scheme.Γ ⋙ twF q i).map g.op).hom ((twRel q i Γ(U, ⊤)).mkQ (c • Finsupp.single ζ 1)) = 0 →
        ((Scheme.Γ ⋙ twF q i).map (k ≫ g).op).hom ((twRel q i Γ(U, ⊤)).mkQ (c • Finsupp.single ζ 1)) = 0 := by
      intro V W g k hg
      change ((Scheme.Γ ⋙ twF q i).map (g.op ≫ k.op)).hom _ = 0
      rw [Functor.map_comp, ModuleCat.hom_comp]
      exact (congrArg (ModuleCat.Hom.hom ((Scheme.Γ ⋙ twF q i).map k.op)) hg).trans (map_zero _)
    obtain ⟨V, g, -, -, ⟨v, -⟩, hV⟩ := (GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover U _ hmono).mp hl u
    have hV' : (c • Submodule.Quotient.mk (Finsupp.single (ζ.map g.appTop.hom) 1) :
        (Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q i Γ(V, ⊤)) = 0 := by
      refine Eq.trans ?_ hV
      change _ = Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.appTop.hom) (c • Finsupp.single ζ 1))
      rw [Finsupp.smul_single, Finsupp.mapDomain_single, ← Finsupp.smul_single, Submodule.Quotient.mk_smul]
    haveI : Nonempty (⊤ : V.Opens) := ⟨⟨v, trivial⟩⟩
    haveI : Nontrivial Γ(V, ⊤) := Scheme.component_nontrivial V ⊤
    obtain ⟨φ, hφ⟩ := (GlobalTheory.T.tateTwistModule_free_and_generator_summand q i Γ(V, ⊤)).2 (ζ.map g.appTop.hom)
    have hc := congrArg φ hV'
    rw [map_nsmul, hφ, map_zero, nsmul_eq_mul, mul_one] at hc
    have hd := congrArg ULift.down hc
    rw [ULift.down_natCast] at hd
    exact (ZMod.natCast_eq_zero_iff c q).mp hd
  have h6 : ∀ (M : Shv (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec M U),
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom)) →
      (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val →
        e U ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • e U ζ) →
      ∃! φ : tw q i ⟶ M, ∀ U ζ, Sec.map φ (twGen i ζ) = e U ζ := by
    intro M e hnat hrel
    let lin : ∀ U : Scheme.{0}, (Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] M.obj.obj (op U) :=
      fun U => Finsupp.linearCombination (ULift.{1} (ZMod q)) (e U)
    have lin_single : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), lin U (Finsupp.single ζ 1) = e U ζ := by
      intro U ζ
      simp only [lin, Finsupp.linearCombination_single, one_smul]
    have hker : ∀ U : Scheme.{0}, twRel q i Γ(U, ⊤) ≤ LinearMap.ker (lin U) := by
      intro U
      refine Submodule.span_le.mpr ?_
      rintro x ⟨ζ, ξ, a, h, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, lin_single, ← Finsupp.smul_single_one, map_smul, lin_single,
        hrel U ζ ξ a h, ulift_zmod_smul_eq_val_nsmul, sub_self]
    let φ0 : Scheme.Γ ⋙ twF q i ⟶ M.obj :=
      { app := fun X => ModuleCat.ofHom ((twRel q i Γ(X.unop, ⊤)).liftQ (lin X.unop) (hker X.unop))
        naturality := by
          intro X Y f
          apply ModuleCat.hom_ext
          apply Submodule.linearMap_qext
          apply Finsupp.lhom_ext'
          intro ξ
          apply LinearMap.ext_ring
          change lin Y.unop (Finsupp.mapDomain (Prim.map f.unop.appTop.hom) (Finsupp.single ξ 1)) =
            (M.obj.map f).hom (lin X.unop (Finsupp.single ξ 1))
          erw [Finsupp.mapDomain_single]
          rw [lin_single]
          exact ((congrArg (M.obj.map f).hom (lin_single X.unop ξ)).trans (hnat Y.unop X.unop f.unop ξ)).symm }
    obtain ⟨ψ, hψ, huniq⟩ := S.2.2 M φ0
    refine ⟨ψ, fun U ζ => ?_, fun φ' hφ' => huniq φ' ?_⟩
    · have := congrArg (fun t => (t.app (op U)).hom
        (Submodule.Quotient.mk (p := twRel q i Γ(U, ⊤)) (Finsupp.single ζ 1))) hψ
      exact this.trans (lin_single U ζ)
    · apply NatTrans.ext
      funext X
      apply ModuleCat.hom_ext
      apply Submodule.linearMap_qext
      apply Finsupp.lhom_ext'
      intro ξ
      apply LinearMap.ext_ring
      exact (hφ' X.unop ξ).trans (lin_single X.unop ξ).symm
  exact ⟨h1, h2, h3, h4, h5, h6⟩
