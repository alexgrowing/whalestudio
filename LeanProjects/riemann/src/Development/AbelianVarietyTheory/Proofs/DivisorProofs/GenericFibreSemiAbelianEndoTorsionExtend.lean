import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatEnd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

noncomputable section

namespace GlobalTheory.Poinc.FibLat

theorem genFibre_endo_torsion : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), (U₀ : Set M.Z).Nonempty → ∃ (A₀ : Over (Sp Ω)) (_ : GrpObj A₀) (a₀ : A₀.left ⟶ ρ.P.A.left) (ψ : A₀.left ⟶ FinalForm.G.left), IsGrpPullback A₀ ρ.P.A (spMap S.R.val.toRingHom) a₀ ∧ IsGrpPullback A₀ FinalForm.G M.pt ψ ∧ (∀ e : ρ.P.A ⟶ ρ.P.A, IsMonHom e → ∃ F : FinalForm.G ⟶ FinalForm.G, IsMonHom F ∧ ∀ e₀ : A₀ ⟶ A₀, e₀.left ≫ a₀ = a₀ ≫ e.left → e₀.left ≫ ψ = ψ ≫ F.left) ∧ ∀ b : S.Gam, ∃ gγ : Over.mk M.pt ⟶ FinalForm.G, gγ ^ (S.r * S.N) = 1 ∧ (∀ w : Sp Ω ⟶ A₀.left, w ≫ A₀.hom = 𝟙 _ → w ≫ a₀ = spMap S.R.val.toRingHom ≫ (ρ.pt b).left → w ≫ ψ = gγ.left) ∧ ∀ z, b ∈ S.HH M z → ExtNear gγ z := by
  intro o Ω _ _ _ S ρ M U₀ EE FinalForm hU
  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hU (x := w) trivial
  let x : Sp Ω ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι M.pt hr
  have hx : x ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  let Q := (Over.pullback FinalForm.u₀).obj ρ.P.A
  let ν : pullback FinalForm.G.hom M.pt ⟶ pullback ρ.P.A.hom FinalForm.u₀ :=
    FinalForm.cart.1.lift (pullback.fst FinalForm.G.hom M.pt) (pullback.snd FinalForm.G.hom M.pt ≫ x)
             (by rw [pullback.condition, Category.assoc, hx])
  have hν₁ : ν ≫ FinalForm.φ = pullback.fst FinalForm.G.hom M.pt := FinalForm.cart.1.lift_fst _ _ _
  have hν₂ : ν ≫ Q.hom = pullback.snd FinalForm.G.hom M.pt ≫ x := FinalForm.cart.1.lift_snd _ _ _
  have gA := isGrpPullback_pullback FinalForm.G M.pt
  have gη : IsGrpPullback ((Over.pullback M.pt).obj FinalForm.G) FinalForm.G (x ≫ U₀.ι) (ν ≫ FinalForm.φ) :=
    gA.congr hx.symm hν₁.symm
  have gν : IsGrpPullback ((Over.pullback M.pt).obj FinalForm.G) Q x ν := FinalForm.cart.cancel gη hν₂
  have gψ := gν.comp (isGrpPullback_pullback ρ.P.A FinalForm.u₀)
  have gψ' : IsGrpPullback ((Over.pullback M.pt).obj FinalForm.G) ρ.P.A (spMap S.R.val.toRingHom)
      (ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) := gψ.congr (FinalForm.u₀_gen x hx) rfl
  refine ⟨(Over.pullback M.pt).obj FinalForm.G, inferInstance, ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀,
    pullback.fst FinalForm.G.hom M.pt, gψ', gA, ?_, ?_⟩
  · intro e he
    haveI := he
    obtain ⟨w', hw', pa⟩ := GlobalTheory.SymBaseChange.exists_endo gψ' e
    obtain ⟨F, ⟨hF, hFw⟩, -⟩ := FinalForm.endo w' hw'
    refine ⟨F, hF, fun e₀ he₀ => ?_⟩
    have hw'l : w'.left ≫ (ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) = (ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) ≫ e.left := by
      have := congrArg (fun z => z.left) (pa (𝟙 _))
      simpa [pushPt] using this
    have he₀w : e₀ = w' := hom_ext_of_pullback gψ' (he₀.trans hw'l.symm)
    rw [he₀w, ← hFw]
    simp only [Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  · intro b
    have hb : (spMap S.R.val.toRingHom ≫ (ρ.pt b).left) ≫ ρ.P.A.hom = 𝟙 _ ≫ spMap S.R.val.toRingHom := by
      rw [Category.assoc, Over.w (ρ.pt b)]; simp
    let w₀ := gψ'.1.lift _ _ hb
    have hw₁ : w₀ ≫ (ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) = spMap S.R.val.toRingHom ≫ (ρ.pt b).left :=
      gψ'.1.lift_fst _ _ _
    have hw₂ : w₀ ≫ pullback.snd FinalForm.G.hom M.pt = 𝟙 _ := gψ'.1.lift_snd _ _ _
    let sec0 : Over.mk (𝟙 (Sp Ω)) ⟶ (Over.pullback M.pt).obj FinalForm.G := Over.homMk w₀ hw₂
    let V : Over.mk M.pt ⟶ Over.mk (𝟙 (Sp Ω) ≫ M.pt) := Over.homMk (𝟙 _) (by simp)
    let gγ : Over.mk M.pt ⟶ FinalForm.G := V ≫ pushPt gA.1.w sec0
    have hgl : gγ.left = w₀ ≫ pullback.fst FinalForm.G.hom M.pt := by simp [gγ, V, pushPt, sec0]
    refine ⟨gγ, ?_, ?_, ?_⟩
    · have h0 : ρ.pt 0 = 1 := by
        have := ρ.pt_add 0 0
        rw [add_zero] at this
        exact mul_eq_left.1 this.symm
      have hpt : ∀ n : ℕ, (ρ.pt b) ^ n = ρ.pt (n • b) := by
        intro n
        induction n with
        | zero => simp [h0]
        | succ k ih => rw [pow_succ, ih, ← ρ.pt_add, succ_nsmul]
      have hrN : (S.r * S.N) • b = 0 := by
        funext i
        simp
      let U : Over.mk (𝟙 (Sp Ω) ≫ spMap S.R.val.toRingHom) ⟶ baseOver (Sp S.R) :=
        Over.homMk (spMap S.R.val.toRingHom) (by simp)
      have hs : pushPt gψ'.1.w sec0 = U ≫ ρ.pt b := by
        apply Over.OverMorphism.ext
        simp [pushPt, sec0, U, hw₁]
      have hsec : sec0 ^ (S.r * S.N) = 1 := by
        apply GlobalTheory.SymBaseChange.pushPt_injective gψ'
        have e1 : pushPt gψ'.1.w (sec0 ^ (S.r * S.N)) = (pushPt gψ'.1.w sec0) ^ (S.r * S.N) :=
          map_pow (pushHom gψ' _) sec0 _
        have e2 : pushPt gψ'.1.w (1 : Over.mk (𝟙 (Sp Ω)) ⟶ (Over.pullback M.pt).obj FinalForm.G) = 1 :=
          map_one (pushHom gψ' _)
        have e3 : (U ≫ ρ.pt b) ^ (S.r * S.N) = U ≫ (ρ.pt b) ^ (S.r * S.N) :=
          (map_pow (preHom U) (ρ.pt b) _).symm
        have e4 : U ≫ (1 : baseOver (Sp S.R) ⟶ ρ.P.A) = 1 := map_one (preHom U)
        rw [e1, e2, hs, e3, hpt, hrN, h0, e4]
      have f1 : gγ ^ (S.r * S.N) = V ≫ (pushPt gA.1.w sec0) ^ (S.r * S.N) :=
        map_pow (preHom V) _ _
      have f2 : (pushPt gA.1.w sec0) ^ (S.r * S.N) = pushPt gA.1.w (sec0 ^ (S.r * S.N)) :=
        (map_pow (pushHom gA _) sec0 _).symm
      have f3 : pushPt gA.1.w (1 : Over.mk (𝟙 (Sp Ω)) ⟶ (Over.pullback M.pt).obj FinalForm.G) = 1 :=
        map_one (pushHom gA _)
      have f4 : V ≫ (1 : Over.mk (𝟙 (Sp Ω) ≫ M.pt) ⟶ FinalForm.G) = 1 := map_one (preHom V)
      rw [f1, f2, hsec, f3, f4]
    · intro w h1 h2
      have : w = w₀ := gψ'.1.hom_ext (by rw [h2, hw₁]) (by
        show w ≫ pullback.snd FinalForm.G.hom M.pt = w₀ ≫ pullback.snd FinalForm.G.hom M.pt
        rw [hw₂]; exact h1)
      rw [this, hgl]
    · intro z hz
      obtain ⟨W, h, hzW, hh, hx'⟩ := FinalForm.sec z b hz
      refine ⟨W, h, hzW, hh, fun y hy => ?_⟩
      rw [hgl, hx' y (w₀ ≫ ν) hy ?_ ?_, Category.assoc, hν₁]
      · rw [Category.assoc, ← Category.assoc ν, hν₁, pullback.condition, ← Category.assoc, hw₂, Category.id_comp]
      · rw [Category.assoc]; exact hw₁

end GlobalTheory.Poinc.FibLat
