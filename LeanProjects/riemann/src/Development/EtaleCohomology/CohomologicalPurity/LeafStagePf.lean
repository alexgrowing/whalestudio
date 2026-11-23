import Development.EtaleCohomology.CohomologicalPurity.LeafHensCutDef

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.CohomologicalPurity.Hz

theorem Diag.leg_w {A : Type} [CommRing A] {I : Ideal A} (Δ : Diag A I) (c : Cocone Δ.D) {j k : Δ.J} (e : j ⟶ k) :
    (Δ.leg c k).comp (Δ.D.map e).hom = Δ.leg c j :=
  congrArg CommRingCat.Hom.hom (c.w e)

theorem Good.kill {A S : Type} [CommRing A] [CommRing S] {φ : A →+* S} {I : Ideal A}
    (ψ : S →+* A ⧸ I) (hψ : ψ.comp φ = Ideal.Quotient.mk I) : ∀ y ∈ I.map φ, ψ y = 0 := by
  intro y hy
  have h : I.map φ ≤ RingHom.ker ψ := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change ψ (φ a) = 0
    rw [← RingHom.comp_apply, hψ]
    exact Ideal.Quotient.eq_zero_iff_mem.2 ha
  exact h hy

theorem Good.retr_unique {A S : Type} [CommRing A] [CommRing S] {φ : A →+* S} {I : Ideal A} (h : Good φ I)
    (χ χ' : S →+* A ⧸ I) (hχ : χ.comp φ = Ideal.Quotient.mk I) (hχ' : χ'.comp φ = Ideal.Quotient.mk I) : χ = χ' := by
  refine RingHom.ext fun s => ?_
  obtain ⟨a, ha⟩ := h.surj s
  have e1 := Good.kill χ hχ _ ha
  have e2 := Good.kill χ' hχ' _ ha
  rw [map_sub, sub_eq_zero] at e1 e2
  rw [e1, e2, ← RingHom.comp_apply, hχ, ← RingHom.comp_apply, hχ']

theorem stage_fin {A : Type} [CommRing A] {I : Ideal A} (Δ : Diag A I) (c : Cocone Δ.D) (hc : IsColimit c)
    (T : Finset c.pt) : ∃ j, ∀ t ∈ T, t ∈ (Δ.leg c j).range := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨(IsFiltered.nonempty : Nonempty Δ.J).some, by simp⟩
  | insert x T hx ih =>
    obtain ⟨j, hj⟩ := ih
    obtain ⟨k, y, hy⟩ := Concrete.isColimit_exists_rep Δ.D hc x
    refine ⟨IsFiltered.max j k, fun t ht => ?_⟩
    rcases Finset.mem_insert.1 ht with rfl | ht
    · refine ⟨(Δ.D.map (IsFiltered.rightToMax j k)).hom y, ?_⟩
      rw [← RingHom.comp_apply, Δ.leg_w]
      exact hy
    · obtain ⟨z, rfl⟩ := hj t ht
      exact ⟨(Δ.D.map (IsFiltered.leftToMax j k)).hom z, by rw [← RingHom.comp_apply, Δ.leg_w]⟩

theorem stage_ideal {A : Type} [CommRing A] {I : Ideal A} (Δ : Diag A I) (c : Cocone Δ.D) (hc : IsColimit c)
    (η : A →+* c.pt) (hη : ∀ j, (Δ.leg c j).comp (Δ.s j) = η) (j : Δ.J) (x : Δ.D.obj j)
    (hx : Δ.leg c j x ∈ I.map η) : x ∈ I.map (Δ.s j) := by
  let r : ∀ j, Δ.D.obj j →+* A ⧸ I := fun j => (Δ.good j).retr.choose
  have hr : ∀ j, (r j).comp (Δ.s j) = Ideal.Quotient.mk I := fun j => (Δ.good j).retr.choose_spec
  let cc : Cocone Δ.D :=
    { pt := CommRingCat.of (A ⧸ I)
      ι := { app := fun j => CommRingCat.ofHom (r j)
             naturality := fun j k e => by
               apply CommRingCat.hom_ext
               simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, CommRingCat.hom_comp,
                 CommRingCat.hom_ofHom]
               exact (Δ.good j).retr_unique _ _ (by rw [RingHom.comp_assoc, Δ.nat e, hr]) (hr j) } }
  let R : c.pt →+* A ⧸ I := (hc.desc cc).hom
  have hR : ∀ j, R.comp (Δ.leg c j) = r j := fun j => congrArg CommRingCat.Hom.hom (hc.fac cc j)
  have hRη : R.comp η = Ideal.Quotient.mk I := by rw [← hη j, ← RingHom.comp_assoc, hR, hr]
  obtain ⟨a, ha⟩ := (Δ.good j).surj x
  have h1 : Δ.leg c j (x - Δ.s j a) ∈ I.map η := by
    have := Ideal.mem_map_of_mem (Δ.leg c j) ha
    rwa [Ideal.map_map, hη] at this
  have h2 : η a ∈ I.map η := by
    have e : η a = Δ.leg c j x - Δ.leg c j (x - Δ.s j a) := by
      rw [map_sub, sub_sub_cancel, ← RingHom.comp_apply, hη]
    rw [e]
    exact Ideal.sub_mem _ hx h1
  have h3 : Ideal.Quotient.mk I a = 0 := by
    rw [← Good.kill R hRη _ h2, ← RingHom.comp_apply, hRη]
  have haI : a ∈ I := Ideal.Quotient.eq_zero_iff_mem.1 h3
  have e : x = (x - Δ.s j a) + Δ.s j a := by ring
  rw [e]
  exact Ideal.add_mem _ ha (Ideal.mem_map_of_mem _ haI)

theorem LeafStage_of : LeafStage := fun _ _ _ Δ c hc η hη =>
  ⟨stage_fin Δ c hc, stage_ideal Δ c hc η hη⟩

end LateralTheory.CohomologicalPurity.Hz
