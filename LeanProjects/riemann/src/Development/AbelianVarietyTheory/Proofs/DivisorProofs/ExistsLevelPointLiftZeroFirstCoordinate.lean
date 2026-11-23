import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodGens
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusExtensionTorsionLiftZeroStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnAbelianLocusUniformisation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubicalWeilPairingEqAbelianPartImage
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaTestPowerIntegral
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RescalePsiEvenTauBimultIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataNsmulRescaleKeepsLaws
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.LevLift

theorem tauBimult_of_rescale_cube : ∀ {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (g : D.X → (FractionRing R)ˣ), (∀ a a' b : D.X, g (a + a' + b) * g a * g a' * g b = g (a + a') * g (a + b) * g (a' + b)) → (GlobalTheory.PolDeg.rescale D g).TauBimult → D.TauBimult := by
  intro R _ _ D g hg h
  refine (GlobalTheory.PolDeg.QuadIff.bimult_iff D).2 fun a a' b z J hJ => ?_
  have H := (GlobalTheory.PolDeg.QuadIff.bimult_iff (GlobalTheory.PolDeg.rescale D g)).1 h a a' b z J hJ
  have e1 := GlobalTheory.PolDeg.QuadIff.val_tau_rescale D g hJ (a + a') b
  have e2 := GlobalTheory.PolDeg.QuadIff.val_tau_rescale D g hJ a b
  have e3 := GlobalTheory.PolDeg.QuadIff.val_tau_rescale D g hJ a' b
  erw [e1, e2, e3] at H
  have hc := congrArg (GlobalTheory.PolDeg.QuadIff.germU z) (hg a a' b)
  simp only [map_mul] at hc
  open GlobalTheory.PolDeg.QuadIff in
  replace H : germU z (g (a + a' + b)) * (germU z (g (a + a')))⁻¹ * (germU z (g b))⁻¹ * Geo.Tor.val (D.tau (a + a') b) (𝟙 _) z J *
      Geo.Tor.val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)) (𝟙 _) z J =
      germU z (g (a + b)) * (germU z (g a))⁻¹ * (germU z (g b))⁻¹ * Geo.Tor.val (D.tau a b) (𝟙 _) z J *
      (germU z (g (a' + b)) * (germU z (g a'))⁻¹ * (germU z (g b))⁻¹ * Geo.Tor.val (D.tau a' b) (𝟙 _) z J) := H
  have a1 := congrArg Additive.ofMul H
  have a2 := congrArg Additive.ofMul hc
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at a1 a2 ⊢
  linear_combination (norm := abel) a1 - a2

theorem degPre_cocharPoint_nsmul_eq_pow_levelLift {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (x : D.X) (n : ℕ) : D.c (n • x) = D.c x ^ n := by
  have hmul : ∀ a b, D.c (a + b) = D.c a * D.c b := fun a b => (D.c_add a b).trans (Hom.mul_def _ _).symm
  have h0 : D.c 0 = 1 := by
    have h := hmul 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := D.c 0) (by rw [_root_.mul_one]; exact h.symm)
  induction n with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ n ih => rw [succ_nsmul, hmul, ih, pow_succ]

theorem roots_of_pull {W V : Type} [CommRing W] [IsDomain W] [CommRing V] [IsDomain V] (θ : W →+* V) (D₀ : DegPre W)
    (Q : DegPre V) (hD : IsPullDeg θ D₀ Q) (y₀ : D₀.X → (𝟙_ (Over (Sp W)) ⟶ D₀.P.A)) (n : ℕ)
    (hy : ∀ x, D₀.c x = y₀ x ^ n) : ∃ c' : Q.X → (𝟙_ (Over (Sp V)) ⟶ Q.P.A), ∀ χ, c' χ ^ n = Q.c χ := by
  have he := hD.e_hom
  let c'' : Q.X → (𝟙_ (Over (Sp V)) ⟶ (Over.pullback (specOf θ)).obj D₀.P.A) := fun χ =>
    Over.homMk (pullback.lift (specOf θ ≫ (y₀ (hD.xe χ)).left) (𝟙 _)
      (by rw [Category.assoc, Over.w (y₀ (hD.xe χ))]; simp)) (pullback.lift_snd _ _ _)
  refine ⟨fun χ => c'' χ ≫ hD.e.inv, fun χ => ?_⟩
  dsimp only
  rw [← cancel_mono hD.e.hom, pow_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have h1 := GlobalTheory.ZH.MultInt.pow_left_pullback (specOf θ) D₀.P.A (T := 𝟙_ (Over (Sp V))) (T₀ := 𝟙_ (Over (Sp W)))
      (specOf θ) (by simp) (c'' χ) (y₀ (hD.xe χ)) (pullback.lift_fst _ _ _).symm n
    have h2 := hD.c_pr χ
    rw [← hy] at h1
    rw [← h1, Over.comp_left, Category.assoc, h2]
  · exact (Over.w (c'' χ ^ n)).trans (Over.w (Q.c χ ≫ hD.e.hom)).symm

theorem exists_roots_of_pull_mulDeg : ∀ {W V : Type} [CommRing W] [IsDomain W] [CommRing V] [IsDomain V] (θ : W →+* V) (D : DegPre W) (n : ℕ) (Q : DegPre V), IsPullDeg θ (mulDeg D n) Q → ∃ c' : Q.X → (𝟙_ (Over (Sp V)) ⟶ Q.P.A), ∀ χ, c' χ ^ n = Q.c χ := by
  intro W V _ _ _ _ θ D n Q hD
  exact roots_of_pull θ (mulDeg D n) Q hD (fun x : D.X => D.c x) n (fun x : D.X => degPre_cocharPoint_nsmul_eq_pow_levelLift D x n)

theorem exists_lift_torsion_of_pull : ∀ {W V : Type} [CommRing W] [IsDomain W] [CommRing V] [IsDomain V] (θ : W →+* V) (D : DegPre W) (Q : DegPre V) (hD : IsPullDeg θ D Q) (G : Over (Sp W)) [GrpObj G] (φ : G.left ⟶ D.P.A.left), IsGrpPullback G D.P.A (𝟙 _) φ → ∀ (x : 𝟙_ (Over (Sp W)) ⟶ G) (n : ℕ), x ^ n = 1 → ∃ b : TF (R := V) (FractionRing V) ⟶ Q.P.A, b ^ n = 1 ∧ b.left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf θ) = jK V ≫ spMap θ ≫ x.left ≫ φ := by
  intro W V _ _ _ _ θ D Q hD G _ φ hp x n hx
  have he := hD.e_hom
  have hφ : φ ≫ D.P.A.hom = G.hom := by simpa using hp.1.w
  have hxφ : (x.left ≫ φ) ≫ D.P.A.hom = 𝟙 (Sp W) ≫ 𝟙 (Sp W) := by
    rw [Category.assoc, hφ, Over.w x]; simp
  let x₁ : Over.mk (𝟙 (Sp W) ≫ 𝟙 (Sp W)) ⟶ D.P.A := Over.homMk (x.left ≫ φ) hxφ
  have hx₁ : x₁ ^ n = 1 :=
    (GlobalTheory.PsiAbelian.pow_eq_one_iff_of_pull (t' := 𝟙 (Sp W)) rfl hp (x' := x) (x := x₁) rfl).1 hx
  have hj : jFK (R := V) (FractionRing V) = 𝟙 _ := by
    simp [jFK]
  have hc : (jK V ≫ spMap θ ≫ x.left ≫ φ) ≫ D.P.A.hom = (TF (R := V) (FractionRing V)).hom ≫ specOf θ := by
    rw [Category.assoc, Category.assoc, Category.assoc, hφ, Over.w x]
    simp [TF, hj]
  let b'' : TF (R := V) (FractionRing V) ⟶ (Over.pullback (specOf θ)).obj D.P.A :=
    Over.homMk (pullback.lift (jK V ≫ spMap θ ≫ x.left ≫ φ) (TF (R := V) (FractionRing V)).hom hc)
      (pullback.lift_snd _ _ _)
  have hb'' : b'' ^ n = 1 := by
    refine GlobalTheory.UU.ImagePairing.pow_eq_one_of_pullback (specOf θ) (T := Over.mk (𝟙 (Sp W) ≫ 𝟙 (Sp W)))
      (jK V ≫ spMap θ) ?_ (x := x₁) ?_ hx₁
    · simp [TF, hj]
    · simp only [b'', x₁, Over.homMk_left]
      exact pullback.lift_fst _ _ _
  refine ⟨b'' ≫ hD.e.inv, ?_, ?_⟩
  · rw [← cancel_mono hD.e.hom, pow_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id, hb'']
    exact (one_comp _).symm
  · rw [← Over.comp_left_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simp only [b'', Over.homMk_left]
    exact pullback.lift_fst _ _ _

end GlobalTheory.UCanon.LevLift

namespace GlobalTheory.UCanon

open GlobalTheory.UCanon.LevLift in

theorem exists_levPt : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X) (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg iw (mulDeg L.D l.M') (GlobalTheory.PolDeg.rescale Q g)), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivBy L Q oQ iw s ε e g hD → ∀ a : D'.La, ∃ p : QkPt Q (FractionRing V) l.M', IsLevPt L iw hD a p := by
  intro E _ _ _ H D' l c L V _ _ Q _ oQ iw I _ s ε e g hD _ hs hdiv a
  have hM : 1 ≤ l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  letI := H.starRing
  have hB0 : (mulDeg L.D l.M').TauBimult :=
    (GlobalTheory.UCanon.MulDeg.mulDeg_laws L.W L.D (𝓞 E) L.oa H.w0 l.M' L.even L.bimult L.w0 L.gen).2.1
  have hB1 : (GlobalTheory.PolDeg.rescale Q g).TauBimult := GlobalTheory.TauPull.tauBimult_pull hG hD hB0
  have ht : ∀ k, algebraMap V (FractionRing V) (s k) ≠ 0 := fun k h =>
    hs k (IsFractionRing.injective V (FractionRing V) (by rw [h, map_zero]))
  have hq : ∀ k (a a' b : Q.X), ε k (e (a + a' + b)) (H.w0 • e (a + a' + b)) + ε k (e a) (H.w0 • e a) +
      ε k (e a') (H.w0 • e a') + ε k (e b) (H.w0 • e b) = ε k (e (a + a')) (H.w0 • e (a + a')) +
      ε k (e (a + b)) (H.w0 • e (a + b)) + ε k (e (a' + b)) (H.w0 • e (a' + b)) := by
    intro k a a' b
    simp only [map_add, smul_add, LinearMap.add_apply]
    ring
  have hP : ∀ y, ((g y : (FractionRing V)ˣ) : FractionRing V) =
      (∏ k, algebraMap V (FractionRing V) (s k) ^ ((l.M' : ℤ) * ε k (e y) (H.w0 • e y)))⁻¹ := fun y => by
    rw [← hdiv.1 y, Units.val_inv_eq_inv_val, inv_inv]
  have hcube : ∀ a a' b : Q.X, g (a + a' + b) * g a * g a' * g b = g (a + a') * g (a + b) * g (a' + b) := by
    intro a a' b
    apply Units.ext
    simp only [Units.val_mul, hP, ← mul_inv, ← Finset.prod_mul_distrib, ← zpow_add₀ (ht _)]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    congr 1
    linear_combination (l.M' : ℤ) * hq k a a' b
  have hB : Q.TauBimult := tauBimult_of_rescale_cube Q g hcube hB1
  obtain ⟨c', hc'⟩ := exists_roots_of_pull_mulDeg iw L.D l.M' _ hD
  have h0 : L.o.etaA 0 = 1 := by
    have h := L.o.etaA_add 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := L.o.etaA 0) (by rw [_root_.mul_one]; exact h.symm)
  have hn : ∀ n : ℕ, L.o.etaA (n • a) = L.o.etaA a ^ n := by
    intro n
    induction n with
    | zero => rw [zero_smul, pow_zero, h0]
    | succ n ih => rw [succ_nsmul, L.o.etaA_add, ih, pow_succ]
  have hη : L.o.etaA a ^ l.M' = 1 := by
    rw [← hn]
    exact L.o.etaA_ker a
  obtain ⟨b, hb, hbl⟩ := exists_lift_torsion_of_pull iw (mulDeg L.D l.M') _ hD L.o.t.G L.φB L.ab.1 (L.o.etaA a) l.M' hη
  obtain ⟨p, hp0, hpb⟩ := GlobalTheory.T.exists_torusExtension_torsion_lift_zero Q hB l.M' hM c' hc' (FractionRing V) b hb
  exact ⟨p, hp0, by rw [hpb]; exact hbl⟩

end GlobalTheory.UCanon
