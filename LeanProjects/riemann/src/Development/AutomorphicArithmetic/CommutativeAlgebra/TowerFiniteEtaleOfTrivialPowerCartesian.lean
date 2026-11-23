import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits
open UpperTheory.Gal.Int.Geo

set_option maxHeartbeats 800000 in
theorem UpperTheory.tower_finiteEtale_of_trivial_powerCartesian :
    PiZero → PowCart → PiFet := by
  intro h0 hpc p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T N c a hN C
  obtain ⟨ρ, e0, hop, hcl, htr⟩ := h0 p D G L E gb w q r 𝔴 𝔫 S k T N c a hN C
  have hx : (1 : G.GAf) ∈ T.X.Δ := T.X.Δ.one_mem
  have hN' : (N : ℕ) = S.N₀ * c := by
    unfold Site.Num at hN
    exact hN.1
  have hsub : ∀ (n m : ℕ) (g : G.GAf), L.CongOne (n * m) g → L.CongOne n g := by
    intro n m g hg
    unfold GlobalTheory.LKGeo.Link.CongOne at hg ⊢
    intro v hv
    obtain ⟨u, hu, huv⟩ := hg v hv
    exact ⟨m • u, AddSubgroup.nsmul_mem _ hu m, by rw [huv, mul_smul]⟩
  obtain ⟨hy, htr'⟩ : ∃ hy, T.X.tr (T.lev N) _ 1 hx hy ≫ ρ = _ := ⟨_, htr hx (by
    intro u hu
    rw [one_mul, inv_one, mul_one]
    rw [T.3] at hu ⊢
    rw [hN'] at hu
    show u ∈ L.KN S.N₀
    unfold GlobalTheory.LKGeo.Link.KN at hu ⊢
    exact ⟨hsub _ _ _ hu.1, hsub _ _ _ hu.2⟩)⟩
  have hG := S.mπ.3
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback at hG
  have hpb := hG.1
  obtain ⟨hP1, hP2, -⟩ := hpc S.Y.X S.M.X S.M.X S.Y.univ.A S.M.univ.A S.M.univ.A S.π (𝟙 _) S.mπ.φ (𝟙 _)
    hpb.w (by simp) k
  have hPB := hP1 hpb
  have hfinP : IsFinite (GlobalTheory.KS.powMap S.π S.mπ.φ hpb.w k) :=
    MorphismProperty.of_isPullback (P := @IsFinite) hPB.flip S.20
  have hetP : Etale (GlobalTheory.KS.powMap S.π S.mπ.φ hpb.w k) :=
    MorphismProperty.of_isPullback (P := @Etale) hPB.flip S.21
  have hcomm : (GlobalTheory.KS.pow S.Y.univ.A k).hom ≫ S.Y.s =
      GlobalTheory.KS.powMap S.π S.mπ.φ hpb.w k ≫ (GlobalTheory.KS.pow S.M.univ.A k).hom ≫ S.M.s := by
    rw [← Category.assoc, hP2, Category.assoc, S.18]
  have eY : S.pi T C ≫ (GlobalTheory.KS.pow S.Y.univ.A k).hom ≫ S.Y.s = T.X.q (T.lev N) ≫ gen (Ow w) E := by
    rw [hcomm, ← Category.assoc, ← htr', Category.assoc, e0, ← Category.assoc, T.X.10]
  refine ⟨eY, ?_⟩
  have h1 : ((GlobalTheory.KS.pow S.Y.univ.A k).hom ≫ S.Y.s) ≫ 𝟙 _ =
      GlobalTheory.KS.powMap S.π S.mπ.φ hpb.w k ≫ (GlobalTheory.KS.pow S.M.univ.A k).hom ≫ S.M.s := by
    rw [Category.comp_id, hcomm]
  have h2 : gen (Ow w) E ≫ 𝟙 _ = 𝟙 _ ≫ gen (Ow w) E := by
    rw [Category.comp_id, Category.id_comp]
  let hm := pullback.map ((GlobalTheory.KS.pow S.Y.univ.A k).hom ≫ S.Y.s) (gen (Ow w) E)
    ((GlobalTheory.KS.pow S.M.univ.A k).hom ≫ S.M.s) (gen (Ow w) E)
    (GlobalTheory.KS.powMap S.π S.mπ.φ hpb.w k) (𝟙 _) (𝟙 _) h1 h2
  have h3 : gen (Ow w) E = 𝟙 _ ≫ gen (Ow w) E := (Category.id_comp _).symm
  have hmF : IsFinite hm := MorphismProperty.pullback_map (P := @IsFinite) hfinP inferInstance hcomm h3
  haveI := hetP
  have hmU : FormallyUnramified hm :=
    MorphismProperty.pullback_map (P := @FormallyUnramified) inferInstance inferInstance hcomm h3
  have hkey : pullback.lift (S.pi T C) (T.X.q (T.lev N)) eY ≫ hm =
      T.X.tr _ _ 1 hx hy ≫ pullback.lift ρ _ e0 := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst, htr']
      simp only [hm, pullback.lift_fst_assoc, pullback.map, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd, T.X.10]
      simp only [hm, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
  haveI := hop
  haveI := hcl
  haveI := T.X.13 _ _ hx hy
  haveI := T.X.14 _ _ hx hy
  have hcomp : IsFinite (pullback.lift (S.pi T C) (T.X.q (T.lev N)) eY ≫ hm) ∧
      Etale (pullback.lift (S.pi T C) (T.X.q (T.lev N)) eY ≫ hm) := by
    rw [hkey]
    exact ⟨inferInstance, inferInstance⟩
  haveI := hcomp.1
  haveI := hcomp.2
  exact ⟨IsFinite.of_comp _ hm, Etale.of_comp _ hm⟩
