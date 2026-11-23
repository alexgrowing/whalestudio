import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopLevExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRowFormPrescribedValuesClassRepresentativeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoefficientVectorReadingRealRepresentationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReadingVectorFixedByClassStabiliserCharacterStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.AdForm.exists_readsG_of_level : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ : ℕ → ℂ), PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (a : I.ι), ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → ∀ f : CXP R P t, ∃ G', ReadsG K eW j g.bT G' f.1 := by
  intro B X I hI hP l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ hX j hj P t a bad K eW hR heW hb hL f

  have hv : ∀ c : (I.stX a).Cl, ∃ w ∈ Formalism.L2.DIV.VV ℂ (I.perIn u a).sgT, ∀ v h, GlobalTheory.Core.Rk.Top.HasMat h (K.y c).1 →
      f.1 v (h * g.bT) = Formalism.L2.DIV.pairB (I.perIn u a).sgT (Formalism.L2.Col.polOf (GlobalTheory.Mem.Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (Formalism.L2.Forms.shiftOf (I.perIn u a).sgT) (GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) (j v)) w := by
    intro c
    obtain ⟨h₀, hh₀⟩ := GlobalTheory.Core.Rk.Top.Model.hasMat_exists (D := I.rec7 l Z) (K.y c)
    obtain ⟨w, hw, e⟩ := GlobalTheory.T.exists_coefficientVector_reading_realRepresentation_form I l Z u a R.MX j hj ((LinearMap.proj (h₀ * g.bT)).comp f.1)
    refine ⟨w, hw, fun v h hh => ?_⟩
    rw [GlobalTheory.Core.Rk.Top.Model.hasMat_pt hh hh₀]
    exact e v
  choose w hw hwv using hv
  obtain ⟨G', hG'⟩ := GlobalTheory.T.exists_rowForm_prescribed_values_class_representatives (I.perIn u a) B.fields.emb B.embLL (fun _ => rfl) w hw
    (fun c s => GlobalTheory.T.readingVector_fixed_by_class_stabiliser_character I hI hP l Z u R g c₀ hX j hj P t a bad K hR hb hL f c (w c) (hw c) (hwv c) s)
  refine ⟨G', fun c v h hh => ?_⟩
  rw [hwv c v h hh]
  have hz : ∀ c', eW.symm (Pi.single c (j v)) c' = (Pi.single c (j v) : (I.fm l u a).clsP → Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ) c' := by
    intro c'
    funext y'
    have := heW (eW.symm (Pi.single c (j v))) c' y' y' rfl
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  generalize eW.symm (Pi.single c (j v)) = z at hz
  have hzc : z c = j v := by rw [hz c, Pi.single_eq_same]
  have hzo : ∀ c', c' ≠ c → z c' = 0 := fun c' h => by
    rw [hz c']
    exact Pi.single_eq_of_ne h _
  haveI := (l.per u a).step.fin_stab c.1 ((I.perIn u a).S'.rep c)
  have hne : ((Nat.card ((I.perIn u a).S'.Stab c) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  letI := (I.perIn u a).clFin (l.per u a)
  show _ = _ * (∑ c' : (I.perIn u a).S'.Cl, (I.perIn u a).wt c' • (Formalism.L2.DIV.pairB (K := ℂ) (I.perIn u a).sgT).compl₁₂
      (Formalism.L2.Col.polOf (GlobalTheory.Mem.Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (Formalism.L2.Forms.shiftOf (I.perIn u a).sgT)
        (GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) ∘ₗ LinearMap.proj c')
      (LinearMap.proj c' ∘ₗ (I.perIn u a).rd B.fields.emb B.embLL)) z G'
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  erw [Fintype.sum_eq_single c (fun c' hc' => by
    change (I.perIn u a).wt c' * Formalism.L2.DIV.pairB _ (Formalism.L2.Col.polOf _ _ _ (z c')) _ = 0
    rw [hzo c' hc']
    simp only [map_zero, LinearMap.zero_apply, mul_zero])]
  change _ = _ * ((((Nat.card ((I.perIn u a).S'.Stab c) : ℕ) : ℂ)⁻¹) * Formalism.L2.DIV.pairB _ (Formalism.L2.Col.polOf _ _ _ (z c)) (G'.1 c.1 ((I.perIn u a).S'.rep c)))
  rw [hzc, hG' c, ← mul_assoc]
  erw [mul_inv_cancel₀ hne, one_mul]
