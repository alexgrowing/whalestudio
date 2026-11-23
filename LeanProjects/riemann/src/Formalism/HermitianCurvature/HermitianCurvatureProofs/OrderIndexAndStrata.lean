import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PointwiseStabiliserParametrisationBijective

set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.OrderIndexAndStrata

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni)
open Formalism.FourierDecayAlt.S3

noncomputable def tb : MassData Unit where
  g := fun _ => 5
  glk := fun _ => 6
  uk := fun _ => 2
  nn := fun _ => 4
  gg := fun _ => 48
  μKp := fun _ => 6
  μKnatp := fun _ => 3
  μKppp := fun _ => 1
  μSp := fun _ => 3
  μSp' := fun _ => 6
  μSppp := fun _ => 1
  μSppp' := fun _ => 2
  Mp := fun _ => 1
  localVolumeAtPlace := fun _ => 1
  μKo := 2
  μSo := 1
  μSo' := 1
  Mo := 4
  localVolumeArchimedean := 1
  μH := 6
  μH' := 6
  μHpp := 2
  μHpp' := 2
  μN := 1/2
  μN' := 1
  volZZ := 1
  volPP := 1
  al := 1
  volG := 6
  volHa := 2
  volHa' := 3
  volNa := 1
  volNa' := 1
  volB := 1
  volH := 1
  volH' := 1
  volN := 2
  volN' := 1
  Coo := 1
  deg := 1
  dimπ := 1
  dimπ' := 1
  ρ0 := 1/3
  ρ0' := 1/2
  d := 1
  d' := 3/2
  n0c := 1
  supdens := 1
  e1 := 1
  δ := 0
  Kgs2 := 4/5
  KV := 1/2
  Sig := 1/6
  KtopV := 1/2
  IntN := 1
  IntC := 1
  IntOO := 1

theorem tb_all : tb.Pos ∧ tb.InTwoA ∧ tb.InForm ∧ tb.InKernel ∧ tb.InMass ∧ tb.InDens ∧ tb.InTheoremA ∧
    tb.InJacMod ∧ tb.InNu ∧ tb.InInfinity ∧ tb.InVolumes ∧ tb.InLevelS ∧ tb.InMasses ∧ tb.InColumns ∧
    tb.InOrdinary ∧ tb.InTyped ∧ tb.InIndices := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [MassData.Pos, MassData.InTwoA, MassData.InForm, MassData.InKernel, MassData.InMass, MassData.InDens, MassData.InTheoremA, MassData.InJacMod, MassData.InNu, MassData.InInfinity, MassData.InVolumes, MassData.InLevelS, MassData.InMasses, MassData.InColumns, MassData.InOrdinary, MassData.InTyped, MassData.InIndices, MassData.tt, MassData.Gam1, MassData.ga, MassData.AA, MassData.MM, MassData.μK, MassData.unitLevelVolume, MassData.Smod, MassData.c0, MassData.c0', MassData.μS, MassData.μSpp, MassData.μS', MassData.μSpp', MassData.Dstar, MassData.μKpp, MassData.GS, tb, Finset.univ_unique, Finset.prod_singleton]

theorem tb_sharp : tb.GS = (1 + tb.δ) * tb.e1 * tb.tt * (tb.d * tb.d' / tb.Dstar) ∧ tb.Gam1 = 3 ∧
    tb.GS = 4/5 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [MassData.Pos, MassData.InTwoA, MassData.InForm, MassData.InKernel, MassData.InMass, MassData.InDens, MassData.InTheoremA, MassData.InJacMod, MassData.InNu, MassData.InInfinity, MassData.InVolumes, MassData.InLevelS, MassData.InMasses, MassData.InColumns, MassData.InOrdinary, MassData.InTyped, MassData.InIndices, MassData.tt, MassData.Gam1, MassData.ga, MassData.AA, MassData.MM, MassData.μK, MassData.unitLevelVolume, MassData.Smod, MassData.c0, MassData.c0', MassData.μS, MassData.μSpp, MassData.μS', MassData.μSpp', MassData.Dstar, MassData.μKpp, MassData.GS, tb, Finset.univ_unique, Finset.prod_singleton]

theorem mainSharp : MainSharp := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := tb_all
  exact ⟨Unit, inferInstance, tb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, by rw [tb_sharp.2.2]; norm_num, tb_sharp.1⟩

theorem unitStratumTotal : UnitStratumTotal := by
  intro volNo volJH volKpp volOm q r hNo hJH hKpp hOm
  rw [hOm]
  field_simp <;> ring

theorem nn0FromMass : DensityFromMassFormula := by
  intro P _ B hB
  obtain ⟨hp, hμKo, -, -, -, hU00o, -, -, -, -, -, -, hvolZZ, -, hal, -, -, -, -, -, -, -, -, -, -,
    hCoo, -⟩ := hB
  have hU : 0 < B.unitLevelVolume :=
    mul_pos hU00o (Finset.prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.2.2.2.2.2)
  have hK : 0 < B.μK := mul_pos hμKo (Finset.prod_pos fun p _ => (hp p).2.2.2.2.2.1)
  have h1 := hU.ne'
  have h2 := hK.ne'
  have h3 := hal.ne'
  have h4 := hvolZZ.ne'
  have h5 := hCoo.ne'
  simp only [MassData.nn0, MassData.AA]
  field_simp <;> ring

theorem rOrderIndex : ROrderIndex := by
  intro o _ _ _
  have hs : Function.Surjective ((IsLocalRing.residue o).comp
      ((RingHom.fst o o).comp (ROrd o).subtype)) := by
    intro y
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨⟨(a, a), by simp [ROrd]⟩, rfl⟩
  exact Nat.card_congr (RingHom.quotientKerEquivOfSurjective hs).toEquiv

theorem kppCorner (hNU : NUExplicit) : KppCorner := by
  intro o _ _ _ ϖ hϖ r k j hj
  have h0 : b31 (j.map (IsLocalRing.residue o)) = 0 := ((hNU _ r k _).1 hj.2).2.2.2.1
  have hmax : IsLocalRing.maximalIdeal o = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hdiv : ∀ a b, ϖ ∣ b31 j a b := by
    intro a b
    have hr : IsLocalRing.residue o (b31 j a b) = 0 := by
      have := congrFun (congrFun h0 a) b
      simpa [b31] using this
    rw [IsLocalRing.residue_eq_zero_iff, hmax, Ideal.mem_span_singleton] at hr
    exact hr
  choose X hX using hdiv
  exact ⟨Matrix.of X, by ext a b; simp [hX a b]⟩

theorem det_mid {A : Type} [CommRing A] {r k : ℕ} (x : Matrix (Idx r k) (Idx r k) A) (hx : IsUnit x.det)
    (h21 : b21 x = 0) (h31 : b31 x = 0) (h32 : b32 x = 0) : IsUnit (b22 x).det := by
  have e21 : ∀ i j, x (Sum.inr (Sum.inl i)) (Sum.inl j) = 0 := fun i j => by
    simpa [b21] using congrFun (congrFun h21 i) j
  have e31 : ∀ i j, x (Sum.inr (Sum.inr i)) (Sum.inl j) = 0 := fun i j => by
    simpa [b31] using congrFun (congrFun h31 i) j
  have e32 : ∀ i j, x (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl j)) = 0 := fun i j => by
    simpa [b32] using congrFun (congrFun h32 i) j
  have hx' : x = Matrix.fromBlocks (b11 x) (Matrix.fromCols (b12 x) (b13 x)) 0
      (Matrix.fromBlocks (b22 x) (b23 x) 0 (b33 x)) := by
    ext i j
    rcases i with i | i | i <;> rcases j with j | j | j <;>
      simp [b11, b12, b13, b22, b23, b33, e21, e31, e32]
  have hdet : x.det = (b11 x).det * ((b22 x).det * (b33 x).det) := by
    conv_lhs => rw [hx']
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁]
  rw [hdet] at hx
  exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right hx)

theorem mid_form {A : Type} [CommRing A] {k : ℕ} (y : Matrix (Mid k) (Mid k) A) (hy : IsUnit y.det)
    (c22 : ∀ a, y a (Sum.inr ()) = if a = Sum.inr () then 1 else 0)
    (r22 : ∀ b, y (Sum.inr ()) b = if b = Sum.inr () then 1 else 0) :
    ∃ h, IsUnit h.det ∧ y = midEmb h := by
  have hy' : y = midEmb (Matrix.of fun a b => y (Sum.inl a) (Sum.inl b)) := by
    ext (a | ⟨⟩) (b | ⟨⟩)
    · simp [midEmb]
    · simpa [midEmb] using c22 (Sum.inl a)
    · simpa [midEmb] using r22 (Sum.inl b)
    · simpa [midEmb] using c22 (Sum.inr ())
  refine ⟨_, ?_, hy'⟩
  rw [hy', Formalism.FourierDecayAlt.P.S3x1.midEmb_det] at hy
  exact hy

theorem sFrame (hS : SExplicit) : SIsFrameStabiliser := by
  intro A _ r k x hx
  rw [hS]
  constructor
  · rintro ⟨h11, h33, h21, h31, h32, h, hh, h22⟩
    refine ⟨⟨h11, h21, h31, fun a => ?_, fun a => ?_⟩, ⟨h33, h32, fun b => ?_, fun b => ?_⟩⟩
    · rw [h22]; rcases a with a | ⟨⟩ <;> simp [midEmb]
    · simp [h32]
    · rw [h22]; rcases b with b | ⟨⟩ <;> simp [midEmb]
    · simp [h21]
  · rintro ⟨⟨h11, h21, h31, hc, -⟩, ⟨h33, h32, hr, -⟩⟩
    obtain ⟨h, hh, he⟩ := mid_form (b22 x) (det_mid x hx h21 h31 h32) hc hr
    exact ⟨h11, h33, h21, h31, h32, h, hh, he⟩

theorem isUpUni_one' {A : Type} [CommRing A] {n : ℕ} : IsUpUni (1 : Matrix (Fin n) (Fin n) A) := by
  exact Formalism.DoubleCosetMeasures.isUpUni_one (K := A)

theorem pointwise_stabiliser_of_explicit (hS : SExplicit) : FrameStabiliserPointwise := by
  intro A _ r k x hx
  unfold IsInertiaInfiniteCyclotomic
  rw [hS]
  constructor
  · rintro ⟨⟨-, -, h21, h31, h32, h, -, h22⟩, h11, h33, h12, h23⟩
    have E11 : ∀ a b, x (Sum.inl a) (Sum.inl b) = (1 : Matrix (Fin r) (Fin r) A) a b :=
      fun a b => by simpa [b11] using congrFun (congrFun h11 a) b
    have E33 : ∀ a b, x (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inr b)) = (1 : Matrix (Fin r) (Fin r) A) a b :=
      fun a b => by simpa [b33] using congrFun (congrFun h33 a) b
    have E21 : ∀ a b, x (Sum.inr (Sum.inl a)) (Sum.inl b) = 0 :=
      fun a b => by simpa [b21] using congrFun (congrFun h21 a) b
    have E31 : ∀ a b, x (Sum.inr (Sum.inr a)) (Sum.inl b) = 0 :=
      fun a b => by simpa [b31] using congrFun (congrFun h31 a) b
    have E32 : ∀ a b, x (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inl b)) = 0 :=
      fun a b => by simpa [b32] using congrFun (congrFun h32 a) b
    have E22 : ∀ a b, x (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl b)) = midEmb h a b :=
      fun a b => by simpa [b22] using congrFun (congrFun h22 a) b
    have E12 : ∀ a, x (Sum.inl a) (Sum.inr (Sum.inl (Sum.inr ()))) = 0 :=
      fun a => by simpa [b12] using h12 a
    have E23 : ∀ b, x (Sum.inr (Sum.inl (Sum.inr ()))) (Sum.inr (Sum.inr b)) = 0 :=
      fun b => by simpa [b23] using h23 b
    refine ⟨fun i b => ?_, fun i => ?_, fun a i => ?_, fun i => ?_⟩
    · rcases i with i | i | i
      · rw [E11]; simp [Matrix.one_apply]
      · rw [E21]; simp
      · rw [E31]; simp
    · rcases i with i | (i | ⟨⟩) | i
      · rw [E12]; simp
      · rw [E22]; simp [midEmb]
      · rw [E22]; simp [midEmb]
      · rw [E32]; simp
    · rcases i with i | i | i
      · rw [E31]; simp
      · rw [E32]; simp
      · rw [E33]; simp [Matrix.one_apply]
    · rcases i with i | (i | ⟨⟩) | i
      · rw [E21]; simp
      · rw [E22]; simp [midEmb]
      · rw [E22]; simp [midEmb]
      · rw [E23]; simp
  · rintro ⟨C1, C2, C3, C4⟩
    have h21 : b21 x = 0 := by ext a b; simpa [b21] using C1 (Sum.inr (Sum.inl a)) b
    have h31 : b31 x = 0 := by ext a b; simpa [b31] using C1 (Sum.inr (Sum.inr a)) b
    have h11 : b11 x = 1 := by ext a b; simpa [b11, Matrix.one_apply] using C1 (Sum.inl a) b
    have h32 : b32 x = 0 := by ext a b; simpa [b32] using C3 a (Sum.inr (Sum.inl b))
    have h33 : b33 x = 1 := by
      ext a b; simpa [b33, Matrix.one_apply] using C3 a (Sum.inr (Sum.inr b))
    have h12 : ∀ a, b12 x a (Sum.inr ()) = 0 := fun a => by simpa [b12] using C2 (Sum.inl a)
    have h23 : ∀ b, b23 x (Sum.inr ()) b = 0 := fun b => by
      simpa [b23] using C4 (Sum.inr (Sum.inr b))
    have c22 : ∀ a, b22 x a (Sum.inr ()) = if a = Sum.inr () then 1 else 0 := by
      intro a
      rcases a with a | ⟨⟩
      · simpa [b22] using C2 (Sum.inr (Sum.inl (Sum.inl a)))
      · simpa [b22] using C2 (Sum.inr (Sum.inl (Sum.inr ())))
    have r22 : ∀ b, b22 x (Sum.inr ()) b = if b = Sum.inr () then 1 else 0 := by
      intro b
      rcases b with b | ⟨⟩
      · simpa [b22] using C4 (Sum.inr (Sum.inl (Sum.inl b)))
      · simpa [b22] using C4 (Sum.inr (Sum.inl (Sum.inr ())))
    obtain ⟨h, hh, he⟩ := mid_form (b22 x) (det_mid x hx h21 h31 h32) c22 r22
    refine ⟨⟨?_, ?_, h21, h31, h32, h, hh, he⟩, h11, h33, h12, h23⟩
    · rw [h11]; exact isUpUni_one'
    · rw [h33]; exact isUpUni_one'

end Formalism.FourierDecayAlt.P.OrderIndexAndStrata

theorem Formalism.FourierDecayAlt.P.frame_stabiliser_characterisation : Formalism.FourierDecayAlt.S3.SIsFrameStabiliser :=
  Formalism.FourierDecayAlt.P.OrderIndexAndStrata.sFrame (fun A _ r k x => Formalism.FourierDecayAlt.P.S3x1.isS_iff x)

theorem Formalism.FourierDecayAlt.P.pointwise_stabiliser_characterisation : Formalism.FourierDecayAlt.S3.FrameStabiliserPointwise :=
  Formalism.FourierDecayAlt.P.OrderIndexAndStrata.pointwise_stabiliser_of_explicit (fun A _ r k x => Formalism.FourierDecayAlt.P.S3x1.isS_iff x)

theorem Formalism.FourierDecayAlt.P.frame_level_exists_alt : Formalism.FourierDecayAlt.S3.FrameLevelExists :=
  by
  intro o _ _ r k
  obtain ⟨B, hB⟩ := Formalism.FourierDecayAlt.P.S3x1.pointwise_stabiliser_is_subgroup (A := IsLocalRing.ResidueField o) (r := r) (k := k)
  refine ⟨⟨B.comap (Formalism.FourierDecayAlt.S3.red o (Formalism.FourierDecayAlt.S3.Idx r k)), fun x => ?_⟩⟩
  rw [Subgroup.mem_comap, hB]
  constructor
  · intro hx
    exact ⟨_, hx, rfl⟩
  · rintro ⟨g, hg, he⟩
    rwa [Units.ext he] at hg

theorem Formalism.FourierDecayAlt.P.corner_group_index_explicit : Formalism.FourierDecayAlt.S3.KppCorner :=
  Formalism.FourierDecayAlt.P.OrderIndexAndStrata.kppCorner (fun A _ r k x => Formalism.FourierDecayAlt.P.S3x1.isNU_iff x)

theorem Formalism.FourierDecayAlt.P.order_index_alt : Formalism.FourierDecayAlt.S3.ROrderIndex :=
  Formalism.FourierDecayAlt.P.OrderIndexAndStrata.rOrderIndex

theorem Formalism.FourierDecayAlt.P.unit_stratum_total_alt : Formalism.FourierDecayAlt.S3.UnitStratumTotal :=
  Formalism.FourierDecayAlt.P.OrderIndexAndStrata.unitStratumTotal

theorem Formalism.FourierDecayAlt.P.density_from_mass : Formalism.FourierDecayAlt.S3.DensityFromMassFormula :=
  Formalism.FourierDecayAlt.P.OrderIndexAndStrata.nn0FromMass

theorem Formalism.FourierDecayAlt.P.mass_formula_sharp : Formalism.FourierDecayAlt.S3.MainSharp :=
  Formalism.FourierDecayAlt.P.OrderIndexAndStrata.mainSharp
