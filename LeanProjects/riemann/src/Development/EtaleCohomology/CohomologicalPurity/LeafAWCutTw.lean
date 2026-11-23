import Development.EtaleCohomology.TateTwists.EtaleTateTwistSectionsLocallyGenerated
import Development.EtaleCohomology.TateTwists.EtaleTorsionCohomologyLocalizationBasic
import Development.EtaleCohomology.TateTwists.EtaleSheafLocalizationPropertiesOfComponents
import Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertibleOrder
import Development.EtaleCohomology.TateTwists.EtaleLocallyKummerRootsOfUnitsOfInvertibleOrder
import Development.EtaleCohomology.TateTwists.TwFGenInjPf
import Development.EtaleCohomology.TateTwists.EtaleKInjectiveExtensionAlongQuasiIsoFromSingle

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.EtaleFoundations

namespace LateralTheory.CohomologicalPurity.LeafAWCutTw

theorem ulift_smul_eq_nsmul {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (r : ULift.{1} (ZMod q)) (m : M) : r • m = r.down.val • m := by
  have : r = ((r.down.val : ℕ) : ULift.{1} (ZMod q)) := by
    cases r with
    | up a =>
      change ULift.up a = ULift.up ((a.val : ℕ) : ZMod q)
      rw [ZMod.natCast_zmod_val]
  conv_lhs => rw [this]
  exact Nat.cast_smul_eq_nsmul _ _ _

theorem twF_map_mk (q : ℕ) (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) (x : Prim q A →₀ ULift.{1} (ZMod q)) :
    ((twF q i).map f).hom (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) x) : (twF q i).obj B) := rfl

theorem twF_single_pow (q : ℕ) [NeZero q] (i : ℤ) (A : CommRingCat.{0}) (ζ ξ : Prim q A) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) (b : ULift.{1} (ZMod q)) :
    (Submodule.Quotient.mk (Finsupp.single ξ b) : (twF q i).obj A) =
      (b.down * ((a ^ i : (ZMod q)ˣ) : ZMod q)).val • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj A) := by
  have hrel : (Submodule.Quotient.mk (Finsupp.single ξ 1) : (twF q i).obj A) =
      Submodule.Quotient.mk (Finsupp.single ζ (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q))) :=
    (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩)
  have e1 : Finsupp.single ξ b = b • Finsupp.single ξ (1 : ULift.{1} (ZMod q)) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  have e2 : Finsupp.single ζ (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q)) =
      (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q)) • Finsupp.single ζ (1 : ULift.{1} (ZMod q)) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [e1, Submodule.Quotient.mk_smul, hrel, e2, Submodule.Quotient.mk_smul, smul_smul]
  exact ulift_smul_eq_nsmul _ _

theorem sec_res {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : M.obj Γ(U, ⊤)) : Sec.res g (ofRings.sec M U x) = ofRings.sec M V ((M.map g.appTop).hom x) :=
  (congrArg (fun f => ModuleCat.Hom.hom f x) ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality g.op)).symm

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U)
    (x : Sec F U) : Sec.res (h ≫ g) x = Sec.res h (Sec.res g x) := by
  simp [Sec.res]

theorem twF_loc (q : ℕ) [NeZero q] (i : ℤ) (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤)) (x : (twF q i).obj Γ(V, ⊤)) :
    Loc V fun W h => ∃ c : ℕ, Sec.res h (ofRings.sec (twF q i) V x) = c • twGen i (ζ.map h.appTop.hom) := by
  have L := LateralTheory.Fin.EtaleLocalPropertyBasicClosure.intersectionNumber_baseChange
  have hZ := (etale_locally_roots_of_unity_structure_of_exists_and_kummer etale_locally_exists_primitive_root_of_unity_of_invertible_order etale_locally_kummer_roots_of_units_of_invertible_order q V).2.1
  have key : Loc V fun W h => ∃ c : ℕ, ((twF q i).map h.appTop).hom x =
      c • (Submodule.Quotient.mk (Finsupp.single (ζ.map h.appTop.hom) 1) : (twF q i).obj Γ(W, ⊤)) := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    induction f using Finsupp.induction with
    | zero =>
      refine L.1 V _ fun W h => ⟨0, ?_⟩
      rw [zero_smul, Submodule.Quotient.mk_zero]
      exact map_zero ((twF q i).map h.appTop).hom
    | single_add ξ b g _ _ ih =>
      refine L.2.1 V _ _ (L.2.2.1 V _ _ (hZ ζ ξ) ih) fun W h ⟨⟨a, ha⟩, ⟨c, hc⟩⟩ =>
        ⟨(b.down * ((a ^ i : (ZMod q)ˣ) : ZMod q)).val + c, ?_⟩
      rw [Submodule.Quotient.mk_add]
      refine (map_add ((twF q i).map h.appTop).hom _ _).trans ?_
      rw [hc, twF_map_mk, Finsupp.mapDomain_single,
        twF_single_pow q i _ (ζ.map h.appTop.hom) (ξ.map h.appTop.hom) a ha b, add_smul]
      rfl
  refine L.2.1 V _ _ key fun W h ⟨c, hc⟩ => ⟨c, ?_⟩
  rw [sec_res, hc]
  unfold twGen ofRings.sec
  exact map_nsmul _ _ _

theorem loc_surj (q : ℕ) (i : ℤ) (U : Scheme.{0}) (y : Sec (tw q i) U) :
    Loc U fun V g => ∃ x : (twF q i).obj Γ(V, ⊤), ofRings.sec (twF q i) V x = Sec.res g y :=
  (LateralTheory.Fin.EtaleSheafificationSectionsLocallyFromPresheaf.intersectionNumber_baseChange (ZMod q) (Scheme.Γ ⋙ twF q i)).1 U y

section Lift
variable {q : ℕ} [NeZero q] (i : ℤ) (M : Shv (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec M U)
  (hn : ∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom))
  (hr : ∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val →
    e U ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • e U ζ)

def liftL (U : Scheme.{0}) : ((Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q i Γ(U, ⊤)) →ₗ[ULift.{1} (ZMod q)] Sec M U :=
  Submodule.liftQ _ (Finsupp.linearCombination _ (e U)) (by
    refine Submodule.span_le.2 ?_
    rintro x ⟨ζ, ξ, a, h, rfl⟩
    change Finsupp.linearCombination _ (e U) _ = 0
    rw [map_sub, Finsupp.linearCombination_single, Finsupp.linearCombination_single, one_smul, hr U ζ ξ a h,
      ulift_smul_eq_nsmul, sub_self])

def liftP : Scheme.Γ ⋙ twF q i ⟶ M.obj where
  app U := ModuleCat.ofHom (liftL i M e hr U.unop)
  naturality U V g := by
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (Finsupp.lhom_ext fun ζ b => ?_))
    revert ζ
    intro (ζ : Prim q Γ(U.unop, ⊤))
    change Finsupp.linearCombination _ (e V.unop) (Finsupp.mapDomain (Prim.map g.unop.appTop.hom) (Finsupp.single ζ b)) =
      Sec.res g.unop (Finsupp.linearCombination _ (e U.unop) (Finsupp.single ζ b))
    rw [Finsupp.mapDomain_single, Finsupp.linearCombination_single, Finsupp.linearCombination_single, ← hn]
    exact (map_smul _ _ _).symm

include hn hr in
theorem lift_ex : ∃ φ : tw q i ⟶ M, ∀ U ζ, Sec.map φ (twGen i ζ) = e U ζ := by
  refine ⟨ObjectProperty.homMk (sheafifyLift Scheme.etaleTopology (liftP i M e hn hr) M.property), fun U ζ => ?_⟩
  have key := congrArg (fun η => (η.app (op U)).hom (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj Γ(U, ⊤)))
    (toSheafify_sheafifyLift Scheme.etaleTopology (liftP i M e hn hr) M.property)
  refine key.trans ?_
  change Finsupp.linearCombination _ (e U) (Finsupp.single ζ 1) = _
  rw [Finsupp.linearCombination_single, one_smul]

end Lift

theorem twSec : EtaleTateTwistSectionsLocallyGenerated := by
  intro q _ i
  have L := LateralTheory.Fin.EtaleLocalPropertyBasicClosure.intersectionNumber_baseChange
  refine ⟨fun U y => ?_, fun U ζ y => ?_, fun U _ ζ c hc => ?_, fun V U g ζ => ?_, fun U ζ ξ a h => ?_,
    fun M e hn hr => ?_⟩
  · refine L.2.2.2.2.1 U _ (L.2.1 U _ _ (loc_surj q i U y) fun V g ⟨x, hx⟩ => ?_)
    by_cases hne : Nonempty (Prim q Γ(V, ⊤))
    · obtain ⟨ζ⟩ := hne
      refine L.2.1 V _ _ (twF_loc q i V ζ x) fun W h ⟨c, hc⟩ => Or.inr ⟨ζ.map h.appTop.hom, c, ?_⟩
      rw [res_comp, ← hx]
      exact hc
    · refine L.1 V _ fun W h => Or.inl ?_
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      have hf : f = 0 := Finsupp.ext fun ζ => absurd ⟨ζ⟩ hne
      have h0 : Sec.res g y = 0 := by
        rw [← hx, hf, Submodule.Quotient.mk_zero]
        unfold ofRings.sec
        exact map_zero _
      rw [res_comp, h0]
      exact map_zero _
  · refine L.2.2.2.2.1 U _ (L.2.1 U _ _ (loc_surj q i U y) fun V g ⟨x, hx⟩ => ?_)
    refine L.2.1 V _ _ (twF_loc q i V (ζ.map g.appTop.hom) x) fun W h ⟨c, hc⟩ => ⟨c, ?_⟩
    have hp : (ζ.map g.appTop.hom).map h.appTop.hom = ζ.map (h ≫ g).appTop.hom := by
      apply Subtype.ext
      simp [Prim.map]
      rfl
    rw [res_comp, ← hx, ← hp]
    exact hc
  · have h1 : ((c : ZMod q).val • twGen i ζ) = c • twGen i ζ := by
      rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)) c, ulift_smul_eq_nsmul]
      rfl
    have := GenConn.inj_of twF_gen_inj_of q U i ζ (a₁ := (c : ZMod q)) (a₂ := 0) (by
      simp only [h1, hc, ZMod.val_zero, zero_smul])
    exact (ZMod.natCast_eq_zero_iff c q).1 this
  · refine (sec_res (twF q i) g _).trans ?_
    rw [twF_map_mk, Finsupp.mapDomain_single]
    rfl
  · unfold twGen
    have := twF_single_pow q i Γ(U, ⊤) ζ ξ a h 1
    rw [ULift.one_down, one_mul] at this
    refine (congrArg (ofRings.sec (twF q i) U) this).trans ?_
    unfold ofRings.sec
    exact map_nsmul _ _ _
  · obtain ⟨φ, hφ⟩ := lift_ex i M e hn hr
    exact ⟨φ, hφ, fun ψ hψ => TwResExt.twuniq_pf q i M ψ φ fun U ζ => (hψ U ζ).trans (hφ U ζ).symm⟩

end LateralTheory.CohomologicalPurity.LeafAWCutTw
