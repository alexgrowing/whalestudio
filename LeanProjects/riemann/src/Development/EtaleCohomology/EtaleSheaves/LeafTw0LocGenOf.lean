import Development.EtaleCohomology.EtaleSheaves.Geo

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0LocGenPf
open LateralTheory.E.LeafTw0LocGenPfA LateralTheory.E.LeafTw0LocGenPfB

theorem loc_top {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => h V g⟩

theorem loc_finset {ι : Type*} [DecidableEq ι] {U : Scheme.{0}} (s : Finset ι)
    {P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : ∀ i ∈ s, Loc U (P i)) : Loc U fun V g => ∀ i ∈ s, P i V g := by
  induction s using Finset.induction_on with
  | empty => exact loc_top fun _ _ i hi => by simp at hi
  | insert j s hj ih =>
    obtain ⟨S0, h0, hP0⟩ := h j (Finset.mem_insert_self j s)
    obtain ⟨S1, h1, hP1⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨S0 ⊓ S1, Scheme.etaleTopology.intersection_covering h0 h1, fun V g hg i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hP0 V g hg.1
    · exact hP1 V g hg.2 i hi

theorem res_sec {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) {W V : Scheme.{0}}
    (g : W ⟶ V) (x : M.obj Γ(V, ⊤)) :
    Sec.res g (ofRings.sec M V x) = ofRings.sec M W ((M.map g.appTop).hom x) := by
  have := congrArg (fun f => f.hom x) ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality g.op)
  exact this.symm

theorem relq {q : ℕ} {A : CommRingCat.{0}} (ζ ξ : Prim q A) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    (Submodule.Quotient.mk (Finsupp.single ξ 1) : (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 A) =
      Submodule.Quotient.mk (Finsupp.single ζ 1) := by
  rw [Submodule.Quotient.eq]
  refine Submodule.subset_span ⟨ζ, ξ, a, h, ?_⟩
  simp
  rfl

theorem mk_mapDomain {q : ℕ} {A B : CommRingCat.{0}} (f : A ⟶ B) (r : Prim q A →₀ ULift.{1} (ZMod q))
    (ζ0 : Prim q A)
    (hrel : ∀ ξ ∈ r.support, (Submodule.Quotient.mk (Finsupp.single (Prim.map f.hom ξ) 1) :
      (Prim q B →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 B) = Submodule.Quotient.mk (Finsupp.single (Prim.map f.hom ζ0) 1)) :
    (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) r) : (Prim q B →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 B) =
      (r.sum fun _ c => c) • Submodule.Quotient.mk (Finsupp.single (Prim.map f.hom ζ0) 1) := by
  classical
  rw [← Submodule.mkQ_apply, Finsupp.mapDomain, Finsupp.sum, map_sum, Finsupp.sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun ξ hξ => ?_
  rw [← hrel ξ hξ, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Finsupp.smul_single_one]

theorem LeafTw0LocGen_of : LateralTheory.E.LeafTw0LocSplitPf.LeafTw0LocGen := by
  classical
  intro q _ U n a
  have hA : ∀ k, Loc U fun V g => ∃ t : (twF q 0).obj Γ(V, ⊤), ofRings.sec (twF q 0) V t = Sec.res g (a k) := by
    intro k
    exact ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology
      (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)) (U := op U) (a k), fun V g hg => hg⟩
  have hA' := loc_finset (U := U) Finset.univ (fun k _ => hA k)
  refine LateralTheory.E.LeafTensMonoPf.loc_trans hA' fun V g hg => ?_
  choose t ht using fun k => hg k (Finset.mem_univ k)
  obtain ⟨r, hr⟩ : ∃ r : Fin n → (Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)),
      ∀ k, (Submodule.Quotient.mk (r k) : (Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 Γ(V, ⊤)) = t k :=
    ⟨fun k => (Submodule.Quotient.mk_surjective _ (t k : (Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 Γ(V, ⊤))).choose,
     fun k => (Submodule.Quotient.mk_surjective _ (t k : (Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 Γ(V, ⊤))).choose_spec⟩
  rcases isEmpty_or_nonempty (Prim q Γ(V, ⊤)) with hE | ⟨⟨ζ0⟩⟩
  · refine loc_top fun W h => ⟨0, fun _ => 0, fun k => ?_, Or.inl rfl⟩
    rw [zero_smul, LateralTheory.E.LeafTensMonoPf.res_comp, ← ht k, ← hr k, Subsingleton.elim (r k) 0,
      Submodule.Quotient.mk_zero]
    unfold ofRings.sec
    have h0 := map_zero (((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)).app (op V)).hom)
    first
      | exact (congrArg (Sec.res h) h0).trans (map_zero _)
      | (erw [h0]; exact map_zero _)
  · obtain ⟨S, hS, hP⟩ := loc_finset (U := V) (Finset.univ.biUnion fun k => (r k).support) (fun ξ _ => geo V ζ0 ξ)
    refine ⟨S, hS, fun W h hh => ?_⟩
    have hrel := hP W h hh
    refine ⟨twGen 0 (Prim.map h.appTop.hom ζ0), fun k => (r k).sum fun _ c => c, fun k => ?_, Or.inr ⟨_, rfl⟩⟩
    rw [LateralTheory.E.LeafTensMonoPf.res_comp, ← ht k, ← hr k]
    refine (res_sec (twF q 0) h _).trans ?_
    have e1 : ((twF q 0).map h.appTop).hom (Submodule.Quotient.mk (r k)) =
        Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map h.appTop.hom) (r k)) := rfl
    rw [e1, mk_mapDomain h.appTop (r k) ζ0 (fun ξ hξ => ?_)]
    · exact map_smul _ _ _
    · obtain ⟨b, hb⟩ := hrel ξ (Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, hξ⟩)
      exact relq _ _ b hb

end LateralTheory.E.LeafTw0LocGenPf
