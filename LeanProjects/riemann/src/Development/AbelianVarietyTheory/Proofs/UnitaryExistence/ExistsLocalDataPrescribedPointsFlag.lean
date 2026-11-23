import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.LatPAddRight
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.DepLaws
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.SubsingletonRankIndicatorIff

noncomputable section

namespace GlobalTheory.PrescribedPoints

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.DIV.Inh Formalism.MainNotions.DIV.Inh.LocalProvisionModel Formalism.L2.Pj NumberField

def formOf {E : Type} [Field E] [NumberField E] (L : LatB E) (hs : ∀ a b, L.beta a b = L.beta b a)
    (ha : ∀ a a' b, L.beta (a + a') b = L.beta a b + L.beta a' b) : L.Y →ₗ[ℤ] L.Y →ₗ[ℤ] ℝ :=
  (AddMonoidHom.mk' (fun a => (AddMonoidHom.mk' (fun b => L.beta a b)
      (fun b b' => by rw [hs a, ha, hs b, hs b'])).toIntLinearMap)
    (fun a a' => by
      ext b
      simp [ha a a' b])).toIntLinearMap

def LatticeLaws (D : D7) (r j : ℕ) (L : LatB D.host.E) : Prop :=
  (∀ a b, L.beta a b = L.beta b a) ∧ (∀ a a' b, L.beta (a + a') b = L.beta a b + L.beta a' b) ∧
  (∀ (x x' : 𝓞 D.host.E), (x' : D.host.E) = D.host.conj (x : D.host.E) →
    ∀ a b, L.beta (x • a) b = L.beta a (x' • b)) ∧
  (∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ L.Y),
    ∀ x : ι → ℝ, x ≠ 0 → 0 < ∑ i, ∑ k, x i * x k * L.beta (b i) (b k)) ∧
  ∃ ρ : ℕ, Module.finrank ℤ L.Y = 2 * D.R.f * ρ ∧ ρ ≤ j ∧ ρ + j ≤ r

def zeroLattice (D : D7) : LatB D.host.E := ⟨Fin 0 → 𝓞 D.host.E, fun a b => beK D 0 a b⟩

theorem zeroLattice_subsingleton (D : D7) : Subsingleton (zeroLattice D).Y :=
  inferInstanceAs (Subsingleton (Fin 0 → 𝓞 D.host.E))

theorem zeroLattice_laws (D : D7) (r j : ℕ) (h : j ≤ r) : LatticeLaws D r j (zeroLattice D) := by
  refine ⟨fun a b => ?_, fun a a' b => ?_, fun x x' _ a b => ?_, ⟨_, inferInstance, bK D 0, beK_posDef D 0⟩,
    0, finrank_copies D 0, Nat.zero_le _, by omega⟩
  · exact (beK_apply D 0 _ _).trans ((beK_apply D 0 _ _).trans (by simp)).symm
  · exact (congrArg (fun f => f b) (map_add (beK D 0) a a'))
  · exact (beK_apply D 0 _ _).trans ((beK_apply D 0 _ _).trans (by simp)).symm

section

variable (D : D7) (r j p : ℕ) (M : MP D p) (Q : Type) (fl : Q → CF p) (Lt : Q → LatB D.host.E)
  (hL : ∀ y, LatticeLaws D r j (Lt y))

@[reducible] def locWithPoints : Loc D r j p where
  Mdl := Unit
  Xm := ()
  YY := ()
  Xn := fun _ => ()
  Pt := fun _ => Q
  fld := fun y => fl y
  Ylat := fun y => (Lt y).Y
  ylAdd := fun _ => inferInstance
  ylMod := fun _ => inferInstance
  ylFree := fun _ => inferInstance
  ylFin := fun _ => inferInstance
  be := fun y => formOf (Lt y) (hL y).1 (hL y).2.1
  be_symm := fun y => (hL y).1
  be_bal := fun y => (hL y).2.2.1
  be_posDef := fun y => (hL y).2.2.2.1
  yl_rank := fun y => by
    obtain ⟨ρ, h1, h2⟩ := (hL y).2.2.2.2
    exact ⟨ρ, h1, fun _ _ => h2⟩
  Gen := fun _ => M.Gn
  abAt := fun _ => True
  Sh := fun _ => Unit
  IsInv := fun _ => True
  IsLocFree := fun _ => True
  Sec := fun _ => PUnit
  secAdd := fun _ => inferInstance
  H0 := fun _ => ⊤
  nrm := fun _ _ _ => 0
  nrm_nonneg := by exists_prescribed_local_data
  norm_le_one_of_mem_sections := by exists_prescribed_local_data
  GIso := fun _ _ => Empty
  vrat := fun _ _ => 0
  Lb := fun _ => ()
  Lb_inv := by exists_prescribed_local_data
  nrmRef := fun _ _ _ => 0
  DVP := M.Gn
  dvRho := fun _ => 0
  Ext := fun _ => Unit
  Chart := fun _ _ _ => Empty
  chAt := fun _ => True
  chOpen := fun _ => True
  chAbExact := fun _ => True
  chModU := fun _ => True
  chConst := fun _ => True

  PL := Unit
  phiAt := fun _ _ _ => 0
  phiAt_zero := by exists_prescribed_local_data
  divGe := fun _ _ _ _ => True
  FJd := Unit
  Chr := fun _ => Unit
  fjN := fun _ _ _ _ => 0
  Unim := ℕ
  LBG := fun _ => Unit
  LBGq := fun _ => Unit
  resQ := fun _ => ()
  PPq := fun _ => ()
  symmG := fun _ => True
  rigG := fun _ => True
  LBGt := fun _ _ => Unit
  LBB := fun _ _ => Unit
  resGt := fun _ _ => ()
  prPull := fun _ => ()
  principal := fun _ => True
  psiV := fun _ _ => 0
  piPP := ()
  keySh := fun _ => ()
  latStd := fun n => n
  At := fun _ La n => AtM (2 * (D.R.f * r * La)) n
  atAdd := fun _ _ _ => inferInstance
  atFin := fun _ _ _ => inferInstance
  at_tors := fun _ _ _ x => atM_tors _ _ x
  at_card := fun _ _ _ h => atM_card _ _ h
  Th := fun y La n => ((fl y).C)ˣ × Multiplicative (AtM (2 * (D.R.f * r * La)) n)
  thGrp := fun _ _ _ => inferInstance
  ovr := fun _ _ _ => MonoidHom.snd _ _
  ovr_surj := fun _ _ _ x => ⟨(1, x), rfl⟩
  scal := fun _ _ _ => MonoidHom.inl _ _
  scal_inj := fun _ _ _ a b h => congrArg Prod.fst h
  scal_central := fun _ _ _ a g => by
    ext <;> simp [mul_comm]
  ker_ovr := fun _ _ _ g => ⟨fun h => ⟨g.1, Prod.ext rfl h.symm⟩, fun ⟨a, h⟩ => by rw [← h]; rfl⟩
  dl := fun _ _ _ => MulEquiv.prodCongr (MulEquiv.refl _) (MulEquiv.inv _)
  dl_ovr := fun _ _ _ _ => rfl
  dl_scal := fun _ La n a => Prod.ext rfl (inv_one : (1 : Multiplicative (AtM (2 * (D.R.f * r * La)) n))⁻¹ = 1)
  dl_dl := fun _ _ _ g => by
    show (g.1, (g.2⁻¹)⁻¹) = g
    rw [inv_inv]
  Sn := fun _ _ _ => PUnit
  snAdd := fun _ _ _ => inferInstance
  snMod := fun _ _ _ => inferInstance
  act := fun _ _ _ => 1
  act_scal := by exists_prescribed_local_data
  vth := fun _ _ _ => 0
  Jet := fun _ _ _ _ => PUnit
  jAdd := fun _ _ _ _ => inferInstance
  jMod := fun _ _ _ _ => inferInstance
  intJet := fun _ _ _ _ => ⊤
  jet := fun _ _ _ _ => 0
  LieGt := fun _ _ => PUnit
  LieB := fun _ _ => PUnit
  LieT := fun _ _ => PUnit
  lgAdd := fun _ _ => inferInstance
  lbAdd := fun _ _ => inferInstance
  ltAdd := fun _ _ => inferInstance
  resB := fun _ _ => 0
  incT := fun _ _ => 0
  kapGt := fun _ _ _ _ => 0
  kapB := fun _ _ _ _ => 0
  Harm := fun _ => Unit
  SecP := fun _ => Unit
  evA := fun _ _ _ => 0
  evGt := fun _ _ _ => 0
  Tp := fun _ => PUnit
  tpAdd := fun _ => inferInstance
  OmV := fun _ => PUnit
  omAdd := fun _ => inferInstance
  omMod := fun _ => inferInstance
  om := fun _ => ⊤
  ht := fun _ => 0
  IsHTBlowup := fun _ _ => False
  eOmP := fun _ _ _ => ()
  SES := fun _ => Unit
  ExactMod := fun _ _ => True
  htSES := fun _ _ => ()
  nefHT := fun _ _ => True
  nefQ := fun _ => True
  descK := fun _ _ => True
  bdryLoci := fun _ => True
  BT := fun _ => Unit
  extA := fun _ => True
  compat := fun _ _ => True
  Crv := M.Cv
  eDeg := fun c => -∑ᶠ τ, ((∑ i ∈ Finset.Icc 1 j, M.dg c τ i) + -∑ i ∈ Finset.Icc (j + 1) r, M.dg c τ i)
  Pm := fun c => pmM D (M.dg c) (r + j)
  Pm_nonneg := fun c => pmM_nonneg D _ _
  degLie := fun c τ b => if b then -∑ i ∈ Finset.Icc (j + 1) r, M.dg c τ i else ∑ i ∈ Finset.Icc 1 j, M.dg c τ i
  degLdR := fun c μ => -∑ᶠ τ, ∑ i ∈ Finset.Icc 1 r, μ τ i * (M.dg c τ i : ℝ)

@[reducible] def extWithPoints (q₀ : Q) (h₀ : Subsingleton (Lt q₀).Y) :
    ExtA D (locWithPoints D r j p M Q fl Lt hL) where
  FlagData := fun _ => Unit
  flagCl := fun _ _ => ()
  allFlags := ()
  YY_eq := rfl
  Idl := fun _ => Unit
  blowUp := fun _ _ => ()
  powP := fun _ => True
  pbPrinc := fun _ _ => True
  Corr := fun _ _ => Unit
  diagCl := fun _ _ _ => ()
  IvD := fun _ => Unit
  jIdl := fun _ _ => ()
  ZP := fun _ => M.Gn
  spz := fun _ _ => True
  abP := fun _ => True
  inQ := fun _ => False
  isGenP := fun _ => False
  isGenP_ab := fun _ h => h.elim
  gpt := fun η => η
  abAt_iff := fun _ => Iff.rfl
  gpt_notQ := fun _ h => h
  genFin := fun _ => M.fin
  genNe := fun _ => M.ne
  redK := fun _ y => y
  dvRho_pos_iff := fun _ _ => by simp
  genK := fun η => η
  redK_genK := fun _ => rfl
  imgM := fun χ => Empty.elim χ
  imgU := fun χ => Empty.elim χ
  img_spz := fun χ => Empty.elim χ
  imgU_inQ := fun χ => Empty.elim χ
  chAt_imgM := fun χ => Empty.elim χ
  chAbExact_imgU := fun χ => Empty.elim χ
  RFam := fun _ _ => Unit
  chFam := fun _ => ()
  ptK := fun _ _ => q₀
  ptK_good := fun _ _ => ⟨fun _ => rfl, fun _ => h₀⟩
  vpi := fun _ => 1
  vpi_pos := by exists_prescribed_local_data
  ordGe := fun _ _ _ _ => True
  yEta := fun _ => q₀
  yEta_good := fun _ => ⟨fun _ => trivial, fun _ => h₀⟩
  homSh := fun _ _ => ()
  homSh_inv := by exists_prescribed_local_data
  isoSec := fun _ => 0
  nrm_isoSec := fun φ => Empty.elim φ
  isoSymm := fun φ => Empty.elim φ
  vrat_symm := fun φ => Empty.elim φ
  LieV := fun _ => PUnit
  lvAdd := fun _ => inferInstance
  lvMod := fun _ => inferInstance
  lieL := fun _ => ⊤
  eig := fun _ _ => ⊤
  Wst := fun _ _ _ => ⊤
  Wst_le := by exists_prescribed_local_data
  taut := fun _ _ _ => ⊤
  taut_eq := by exists_prescribed_local_data
  nrmIn := fun _ _ _ _ => 0
  nrmRef_def := by exists_prescribed_local_data
  nrm_Lb_def := by exists_prescribed_local_data
  om_smul := by exists_prescribed_local_data
  TC := fun _ => PUnit
  tcAdd := fun _ => inferInstance
  tcMod := fun _ => inferInstance
  iT := fun _ => 0
  iT_span := by exists_prescribed_local_data
  htC := fun _ => 0
  htC_iT := by exists_prescribed_local_data
  psiC := fun _ => 0
  lieGt1 := fun _ => ⊤
  eT := fun _ _ => 0
  HTn := fun _ => Empty
  htEval := fun h => Empty.elim h
  htIdl := fun _ => ()
  IsHTBlowup_def := fun n Z' _ => ⟨fun h => h.elim, fun ⟨h, _⟩ => Empty.elim h⟩
  wFib := fun _ _ _ => ⊤
  htFlags := fun _ => ()
  omSh := fun _ => ()
  omPat := fun _ => ⊤
  omPat_def := fun _ _ _ h => h.elim
  BPt := fun _ => Empty
  bfld := fun _ => M.K
  OmB := fun _ => PUnit
  obAdd := fun _ => inferInstance
  obMod := fun _ => inferInstance
  omB := fun _ => ⊤
  omPB := fun _ => ⊤
  eOmB := fun _ _ => ⊤
  eB := fun _ _ => 0
  YsP := fun _ => Empty
  ysBd := fun _ => True
  FlP := Unit
  hFl := fun _ => ()
  FlCl := Unit
  flMem := fun _ _ => True
  flDim := fun _ => 0
  Sum1 := Unit
  locus := fun _ => ()
  bdryLoci_def := fun _ => ⟨fun _ => ⟨∅, Set.finite_empty, fun x => Empty.elim x, by simp⟩, fun _ => trivial⟩
  CrvS := fun _ => Empty
  degGr := fun _ _ _ => 0
  nefHT_def := fun _ _ => ⟨fun _ C => Empty.elim C, fun _ => trivial⟩
  CrvQ := Empty
  degGrQ := fun _ _ _ => 0
  nefQ_def := fun _ => ⟨fun _ C => Empty.elim C, fun _ => trivial⟩
  degGrD := fun c => M.dg c
  degLdR_def := fun _ _ => rfl
  degLie_f := fun _ _ => rfl
  degLie_alt := fun _ _ => rfl
  eDeg_def := fun _ _ => rfl
  Pm_head := fun c τ i _ h2 => le_trans (le_abs_self _)
    (abs_le_pmM D (M.dg c) (r + j) τ _ (Finset.Icc_subset_Icc le_rfl (by omega)))
  Pm_tail := fun c τ i _ _ => le_trans (neg_le_abs _)
    (abs_le_pmM D (M.dg c) (r + j) τ _ (Finset.Icc_subset_Icc (by omega) (by omega)))

end

@[reducible] def provWithPoints (D : D7) (Dat : Type) (rk jj : Dat → ℕ) (h : ∀ w, 1 ≤ jj w ∧ jj w + 1 ≤ rk w)
    (M : ∀ (_ : Dat) (p : ℕ), MP D p) (Q : Dat → ℕ → Type) (fl : ∀ w p, Q w p → CF p)
    (Lt : ∀ w p, Q w p → LatB D.host.E) (hL : ∀ w p y, LatticeLaws D (rk w) (jj w) (Lt w p y))
    (q₀ : ∀ w p, Q w p) (h₀ : ∀ w p, Subsingleton (Lt w p (q₀ w p)).Y) : ModuliIntegralCharts.Prov D where
  Dat := Dat
  rk := rk
  jj := jj
  jj_range := h
  loc := fun w p => locWithPoints D (rk w) (jj w) p (M w p) (Q w p) (fl w p) (Lt w p) (hL w p)
  ex := fun w p => extWithPoints D (rk w) (jj w) p (M w p) (Q w p) (fl w p) (Lt w p) (hL w p) (q₀ w p) (h₀ w p)
  NgC := fun _ => Unit
  NgC_ne := fun _ => ⟨()⟩
  KF := fun _ _ => Unit
  kfNorm := fun _ _ => 1
  pbKF := fun _ _ _ _ => 0
  levIn := fun _ _ => True
  Xg := fun _ => Unit
  bc := fun _ _ => ()
  DivX := fun _ => Unit
  effD := fun _ => True
  noVertD := fun _ => True
  posBdD := fun _ => True
  ampleOnAbelianBase := fun _ _ _ => True
  Met := fun _ => Unit
  nefFib := fun _ => True
  ampleGen := fun _ => True
  limRA := fun _ => True

end GlobalTheory.PrescribedPoints

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.PrescribedPoints Formalism.MainNotions.DIV.Inh Formalism.MainNotions.DIV.Inh.LocalProvisionModel in

theorem exists_prov_prescribed_points :
    ∀ (D : D7) (Pt : ℕ → ℕ → Type) (fld : ∀ j p, Pt j p → ModuliIntegralCharts.CF p) (L : ∀ j p, Pt j p → LatB D.host.E), (∀ j p y, (∀ a b, (L j p y).beta a b = (L j p y).beta b a) ∧ (∀ a a' b, (L j p y).beta (a + a') b = (L j p y).beta a b + (L j p y).beta a' b) ∧ (∀ (x x' : 𝓞 D.host.E), (x' : D.host.E) = D.host.conj (x : D.host.E) → ∀ a b, (L j p y).beta (x • a) b = (L j p y).beta a (x' • b)) ∧ (∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ (L j p y).Y), ∀ x : ι → ℝ, x ≠ 0 → 0 < ∑ i, ∑ k, x i * x k * (L j p y).beta (b i) (b k)) ∧ ∃ ρ : ℕ, Module.finrank ℤ (L j p y).Y = 2 * D.R.f * ρ ∧ ρ ≤ (D.R.sigW j).1 ∧ ρ + (D.R.sigW j).1 ≤ D.R.r) → ∃ (P : ModuliIntegralCharts.Prov D) (dat : ℕ → P.Dat), ∀ j, 1 ≤ j → j < D.R.m → (P.rk (dat j) = D.R.r ∧ P.jj (dat j) = (D.R.sigW j).1) ∧ ∀ p y, ∃ η : (P.loc (dat j) p).Pt (P.loc (dat j) p).YY, (P.loc (dat j) p).fld η = fld j p y ∧ ∃ e : (P.loc (dat j) p).Ylat η ≃ₗ[𝓞 D.host.E] (L j p y).Y, ∀ a b, (L j p y).beta (e a) (e b) = (P.loc (dat j) p).be η a b := by
  intro D Pt fld L hL
  have hm := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hr : ∀ w : {j : ℕ // 1 ≤ j ∧ j < D.R.m}, 1 ≤ (D.R.sigW w.1).1 ∧ (D.R.sigW w.1).1 + 1 ≤ D.R.r := by
    rintro ⟨w, h1, h2⟩
    simp only [Formalism.BasicNotions.Ranks.sigW, Formalism.BasicNotions.Ranks.r]
    omega
  refine ⟨provWithPoints D {j : ℕ // 1 ≤ j ∧ j < D.R.m} (fun _ => D.R.r) (fun w => (D.R.sigW w.1).1) hr
    (fun _ p => mpTrivialAb D p (nonempty_coefficient_field p).some) (fun w p => Option (Pt w.1 p))
    (fun w p y => y.elim (nonempty_coefficient_field p).some (fld w.1 p))
    (fun w p y => y.elim (zeroLattice D) (L w.1 p))
    (fun w p y => match y with
      | none => zeroLattice_laws D _ _ (by have := hr w; omega)
      | some y => hL w.1 p y)
    (fun _ _ => none) (fun _ _ => zeroLattice_subsingleton D),
    fun j => if h : 1 ≤ j ∧ j < D.R.m then ⟨j, h⟩ else ⟨1, le_rfl, hm⟩, fun j h1 h2 => ?_⟩
  beta_reduce
  rw [dif_pos (And.intro h1 h2)]
  exact ⟨⟨rfl, rfl⟩, fun p y => ⟨some y, rfl, LinearEquiv.refl _ _, fun a b => rfl⟩⟩

end GlobalTheory

end
