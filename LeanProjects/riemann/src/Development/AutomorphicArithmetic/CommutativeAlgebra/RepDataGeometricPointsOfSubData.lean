import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsIsogenyWithKernelSubgroup
import Development.AutomorphicArithmetic.SpecialMaps.QuotObjDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTypeTjIsogeniesRepresentable
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel UpperTheory.QO

noncomputable section

namespace UpperTheory.SectionEquivalence

variable {T U : Scheme.{0}} {G' : Over T} [GrpObj G'] {G : Over U} [GrpObj G] {f : T ⟶ U} {φ : G'.left ⟶ G.left}

private theorem mul_left (hp : IsGrpPullback G' G f φ) (h h' : 𝟙_ (Over T) ⟶ G') {g : T ⟶ U} (hg : 𝟙 T ≫ f = g)
    (x₀ y₀ : Over.mk g ⟶ G) (hx : x₀.left = h.left ≫ φ) (hy : y₀.left = h'.left ≫ φ) :
    (x₀ * y₀).left = (h * h').left ≫ φ := by
  subst hg
  exact hp.2 _ h h' x₀ y₀ hx hy

private def secEquiv (hp : IsGrpPullback G' G f φ) : (𝟙_ (Over T) ⟶ G') ≃* (Over.mk f ⟶ G) where
  toFun h := Over.homMk (h.left ≫ φ) (by
    have e : h.left ≫ G'.hom = 𝟙 T := Over.w h
    show (h.left ≫ φ) ≫ G.hom = f
    rw [Category.assoc, hp.1.w, ← Category.assoc, e]
    exact Category.id_comp f)
  invFun a := (Over.homMk (hp.1.lift a.left (𝟙 T) ((Over.w a).trans (Category.id_comp f).symm))
    (hp.1.lift_snd _ _ _) : Over.mk (𝟙 T) ⟶ G')
  left_inv h := by
    have e : h.left ≫ G'.hom = 𝟙 T := Over.w h
    refine Over.OverMorphism.ext (hp.1.hom_ext ?_ ?_)
    · exact hp.1.lift_fst _ _ _
    · exact (hp.1.lift_snd _ _ _).trans e.symm
  right_inv a := Over.OverMorphism.ext (hp.1.lift_fst _ _ _)
  map_mul' h h' := Over.OverMorphism.ext
    (mul_left hp h h' (Category.id_comp f) _ _ rfl rfl).symm

private theorem secEquiv_left (hp : IsGrpPullback G' G f φ) (h : 𝟙_ (Over T) ⟶ G') :
    (secEquiv hp h).left = h.left ≫ φ := rfl

private theorem secEquiv_comp {H' : Over T} [GrpObj H'] {H : Over U} [GrpObj H] {φ₁ : H'.left ⟶ H.left}
    (hp : IsGrpPullback G' G f φ) (hp₁ : IsGrpPullback H' H f φ₁) (α : G' ⟶ H') (β : G ⟶ H)
    (e : α.left ≫ φ₁ = φ ≫ β.left) (h : 𝟙_ (Over T) ⟶ G') :
    secEquiv hp₁ (h ≫ α) = secEquiv hp h ≫ β := by
  refine Over.OverMorphism.ext ?_
  rw [secEquiv_left, Over.comp_left, Over.comp_left, secEquiv_left, Category.assoc, Category.assoc, e]

end UpperTheory.SectionEquivalence

open UpperTheory.SectionEquivalence

theorem UpperTheory.repData_geometric_points_of_subData :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → D.m = 1 → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (Rd : RepData b N r w j c s o) (Sd : SubData w j o) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ y : Sp k ⟶ Rd.Y.left, y ≫ Rd.Y.hom = x ∧ KerGeo Rd Sd y := by
  intro p _ D R _ _ b N hN hNp hpu hm r w j c hw hr hj hc S _ s o Rd Sd k _ _ x
  obtain ⟨ox, ⟨m⟩⟩ := IsogRep.exists_pull x o (s' := x ≫ s) rfl
  have hp' : IsGrpPullback ox.A o.A x m.φ := m.cart
  letI := Sd.grp
  haveI := Sd.hom
  let Ksub : Subgroup (Over.mk x ⟶ o.A) := (IsMonHom.monoidHom Sd.i (Over.mk x)).range
  let H₀ : Subgroup (𝟙_ (Over (Sp k)) ⟶ ox.A) := Ksub.comap (secEquiv hp').toMonoidHom
  have memH : ∀ h, h ∈ H₀ ↔ InSub Sd.i (secEquiv hp' h) := fun h => Iff.rfl
  have hstab : ∀ (a : D.O), ∀ h ∈ H₀, h ≫ ox.act.act a ∈ H₀ := by
    intro a h hh
    rw [memH] at hh ⊢
    obtain ⟨z, hz⟩ := hh
    obtain ⟨g, hg⟩ := Sd.stable a
    refine ⟨z ≫ g, ?_⟩
    rw [secEquiv_comp hp' hp' _ _ (m.act a) h, Category.assoc, hg, ← Category.assoc, hz]
  have hkill : ∀ h ∈ H₀, ES.KilledBy ox w h := by
    intro h hh c hc
    have hk := Sd.killed _ _ ((memH h).1 hh) c hc
    rw [← secEquiv_comp hp' hp' _ _ (m.act _) h, ← map_one (secEquiv hp')] at hk
    exact (secEquiv hp').injective hk
  have hcard : Nat.card H₀ = Ideal.absNorm w ^ j := by
    haveI := Sd.mono
    haveI := Sd.fin
    haveI := Sd.et
    have hmem : ∀ z : Over.mk x ⟶ Sd.K, (secEquiv hp').symm (z ≫ Sd.i) ∈ H₀ := fun z => by
      rw [memH, MulEquiv.apply_symm_apply]
      exact ⟨z, rfl⟩
    have e1 : H₀ ≃ (Over.mk x ⟶ Sd.K) := by
      refine (Equiv.ofBijective (fun z : Over.mk x ⟶ Sd.K => (⟨_, hmem z⟩ : H₀)) ⟨?_, ?_⟩).symm
      · intro z z' hzz
        have hz := congrArg (fun u : H₀ => secEquiv hp' u.1) hzz
        simp only [MulEquiv.apply_symm_apply] at hz
        exact (cancel_mono Sd.i).1 hz
      · rintro ⟨h, hh⟩
        obtain ⟨z, hz⟩ := (memH h).1 hh
        refine ⟨z, Subtype.ext ?_⟩
        simp only [hz, MulEquiv.symm_apply_apply]
    have e2 : (Over.mk x ⟶ Sd.K) ≃ {t : Spec (CommRingCat.of k) ⟶ Sd.K.left // t ≫ Sd.K.hom = x} :=
      { toFun := fun z => ⟨z.left, by simpa using Over.w z⟩
        invFun := fun t => Over.homMk t.1 t.2
        left_inv := fun z => Over.OverMorphism.ext rfl
        right_inv := fun t => Subtype.ext rfl }
    let pt : ↥(Spec (CommRingCat.of k)) := IsLocalRing.closedPoint k
    obtain ⟨-, hc⟩ := GlobalTheory.FinEt.card_points_eq_finrank Sd.K.hom x pt
    rw [Nat.card_congr (e1.trans e2), hc]
    have hK : (toUnit Sd.K).left = Sd.K.hom := by simpa using Over.w (toUnit Sd.K)
    have hr := Sd.deg.rank (x pt)
    rw [hK] at hr
    exact hr
  obtain ⟨o', ψ, hiso, htj, hker⟩ :=
    UpperTheory.exists_isogeny_with_kernel_subgroup p D R b N hN hNp hpu hm r w j c hw hr hc k (x ≫ s) ox H₀ hstab hkill hcard
  obtain ⟨y, ⟨hy, m₀', m₁, hsq⟩, -⟩ := Rd.univ (Sp k) x ox o' m ψ hiso htj
  subst hy
  refine ⟨y, rfl, ?_⟩
  intro a₀ a ha
  have hp₀ := m₀'.cart
  have hp₁ := m₁.cart
  obtain ⟨mm, hmm⟩ := IsogRep.exists_comp m₀' Rd.m₀
  have hφ : m.φ = m₀'.φ ≫ Rd.m₀.φ := by
    rw [← hmm]
    exact GlobalTheory.T.harrisTaylor_pullback_abelian_map_unique_of_base_eq p D R b N hN hNp _ _ _ _ o ox _ _ m mm rfl
  obtain ⟨h, rfl⟩ : ∃ h, secEquiv hp₀ h = a₀ := ⟨(secEquiv hp₀).symm a₀, MulEquiv.apply_symm_apply _ _⟩
  have haa : a = secEquiv hp' h := by
    apply Over.OverMorphism.ext
    rw [secEquiv_left, hφ, ← Category.assoc, ← secEquiv_left hp₀, ha]
  have hψ1 : secEquiv hp₀ h ≫ Rd.ψ = secEquiv hp₁ (h ≫ ψ) :=
    (secEquiv_comp hp₀ hp₁ ψ Rd.ψ hsq.symm h).symm
  have hkb : ∀ I : Ideal (𝓞 D.F), ES.KilledBy Rd.o₀ I (secEquiv hp₀ h) ↔ ES.KilledBy ox I h := by
    intro I
    refine forall₂_congr fun c _ => ?_
    rw [← secEquiv_comp hp₀ hp₀ _ _ (m₀'.act _) h, ← map_one (secEquiv hp₀),
      (secEquiv hp₀).injective.eq_iff]
  rw [haa, ← memH, ← hker, hψ1, ← map_one (secEquiv hp₁), (secEquiv hp₁).injective.eq_iff]
  simp only [hkb]

end
