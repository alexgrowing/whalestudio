import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WchartCompLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePowerPullbackSectionPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerPullbackSectionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePowerIsoReindexedChartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaledLineBundlePowerIsoGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffPullbackBaseChangeStableSectionBasisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

noncomputable section

namespace GlobalTheory.HomFixMatEx

theorem liftTop (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg)
    (A' : Over (Sp R)) (φA' : A'.left ⟶ A.left) (hpb : IsPullback φA' A'.hom A.hom t) :
    ∃ ψ : A'.left ⟶ (topS Rg ⊗ A).left, ψ ≫ (snd (topS Rg) A).left = φA' := by
  let a0 : A'.left ⟶ (⊤ : (Sp Rg).Opens).toScheme :=
    IsOpenImmersion.lift (⊤ : (Sp Rg).Opens).ι (A'.hom ≫ t) (by simp)
  let X : Over (Sp Rg) := Over.mk (A'.hom ≫ t)
  let a : X ⟶ topS Rg := Over.homMk a0 (by simp only [a0, X, topS, overRes, baseOver, Over.mk_hom, Category.comp_id]; exact IsOpenImmersion.lift_fac _ _ _)
  let b : X ⟶ A := Over.homMk φA' hpb.w
  refine ⟨(lift a b).left, ?_⟩
  rw [← Over.comp_left, lift_snd]
  rfl

theorem zero_comp (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (R : Type) [CommRing R]
    (t : Sp R ⟶ Sp Rg) (A' : Over (Sp R)) [GrpObj A'] (φA' : A'.left ⟶ A.left) (h : IsGrpPullback A' A t φA') :
    zeroPt A' ≫ φA' = t ≫ eSec A := by
  let T : Over (Sp R) := 𝟙_ (Over (Sp R))
  let u : Over.mk (T.hom ≫ t) ⟶ A := Over.homMk ((1 : T ⟶ A').left ≫ φA') (by
    simp only [Over.mk_hom, Category.assoc]
    rw [h.1.w, ← Category.assoc, Over.w])
  have hu : u * u = u := Over.OverMorphism.ext (by
    rw [h.2 T 1 1 u u rfl rfl, _root_.mul_one]; rfl)
  have hu1 : u = 1 := mul_eq_left.1 hu
  have e := congrArg (fun x => Over.Hom.left x) hu1
  simp only [u, Over.homMk_left] at e
  rw [Hom.one_def, Hom.one_def] at e
  simp at e
  exact e
end GlobalTheory.HomFixMatEx

namespace GlobalTheory.HomFixMatEx

theorem res_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens} (e : V ≤ f ⁻¹ᵁ U) (h : V' ≤ V)
    (x : Γ(Y, U)) :
    (X.presheaf.map (homOfLE h).op).hom ((f.appLE U V e).hom x) = (f.appLE U V' (h.trans e)).hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

end GlobalTheory.HomFixMatEx

namespace GlobalTheory.HomFixMat
open GlobalTheory.HomFixMatEx

theorem exists_isMat : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsTest A B L M t A' B' φA' φB' Φ' → ∃ c, IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c := by
  intro Rg _ _ A B _ _ _ _ L M k mA mB bA bB eA eB hH R _ t A' B' _ _ φA' φB' Φ' hT
  obtain ⟨_, _, hL, hM, heA, heB, _, _, _, hbA, _⟩ := hH
  obtain ⟨hpA, hpB, hΦ, hiso⟩ := hT
  obtain ⟨ψA, hψA⟩ := liftTop Rg A R t A' φA' hpA.1
  obtain ⟨ψB, hψB⟩ := liftTop Rg B R t B' φB' hpB.1
  obtain ⟨w, hw⟩ := hiso
  have eg : (Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left = Φ'.left ≫ φB' := by rw [Category.assoc, hψB]
  obtain ⟨α₀, hα₀⟩ : ∃ α₀ : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB), α₀.IsGen := by
    have := GlobalTheory.T.exists_lineBundlePower_iso_reindexed_charts L M φA' Φ'.left φB' k w hw
    show ∃ α₀ : LB.Gen (LB.div (powPull M ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left) (k : ℤ))
      (powPull L (ψA ≫ (snd (topS Rg) A).left) (k : ℤ))), α₀.IsGen
    rw [eg, hψA]; exact this
  have hΦ0 : zeroPt A' ≫ Φ'.left = zeroPt B' := by
    haveI := hΦ
    exact congrArg Over.Hom.left (IsMonHom.one_hom (f := Φ'))
  have hz1 : zeroPt A' ≫ (ψA ≫ (snd (topS Rg) A).left) = t ≫ eSec A := by
    rw [hψA]; exact zero_comp Rg A R t A' φA' hpA
  have hz2 : zeroPt A' ≫ ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left) = t ≫ eSec B := by
    rw [eg, ← Category.assoc, hΦ0]; exact zero_comp Rg B R t B' φB' hpB
  have hzπ : zeroPt A' ≫ A'.hom = 𝟙 (Sp R) := Over.w η[A']
  obtain ⟨α, hα, hrig⟩ := GlobalTheory.T.exists_rescaled_lineBundlePower_iso_generator (Z₀ := Sp Rg) L M (ψA ≫ (snd (topS Rg) A).left)
    ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left) (eSec A) (eSec B) t (zeroPt A') A'.hom k eA eB α₀
    hL hM heA heB hα₀ hzπ hz1 hz2
  have key : ∀ j : Fin mB, ∃ cj : Fin mA → Γ(Sp R, ⊤), ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      ((Φ'.left ≫ ψB).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        (α.s p).val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (by simp)).hom (cj i) *
          (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2) := by
    intro j
    obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_lineBundlePowerPullback_section_pullback M (snd (topS Rg) B).left (Φ'.left ≫ ψB) (k : ℤ) (bB j)
    obtain ⟨s, hs⟩ := GlobalTheory.T.power_pullback_section_exists L M (ψA ≫ (snd (topS Rg) A).left) ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left)
      (k : ℤ) α hα hL hM σ
    obtain ⟨c, hc⟩ := GlobalTheory.T.exists_coeff_pullback_baseChangeStableSectionBasis Rg A L k mA bA hbA R t A' φA' hpA.1 ψA hψA s
    refine ⟨c, fun p => ?_⟩
    have e1 := hs p
    rw [hσ p.1, hc p.2, map_sum] at e1
    erw [res_appLE] at e1
    simp only [map_mul] at e1
    erw [e1]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    · exact res_appLE _ _ _ _
    · exact res_appLE _ _ _ _
  choose cj hcj using key
  exact ⟨fun i j => cj j i, ψA, ψB, α, hψA, hψB, hα, hrig, fun j p => hcj j p⟩

end GlobalTheory.HomFixMat
