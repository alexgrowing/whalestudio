import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Topology

noncomputable section

namespace GlobalTheory.GridJoin

variable {D : D7}
theorem conj_back {G : Type*} [Group G] (b g : G) : b⁻¹ * (b * g * b⁻¹) * b = g := by group

theorem mem_princGL_of_cong {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {I : Ideal (𝓞 E)} (h2 : x ∈ St β)
    {z : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hz : ∀ i j, z i j ∈ Formalism.L2.Herm.intAf F E)
    (e : (β⁻¹ * x * β).1 - 1 = Ideal.absNorm I • z) : x ∈ GlobalTheory.Grid.princGL β I := by
  obtain ⟨y, rfl⟩ := h2
  refine GlobalTheory.Grid.mem_princGL.2 ⟨y, rfl, fun i j => ?_⟩
  have e2 : β⁻¹ * frGL β y * β = intGL F E n y := conj_back β _
  rw [e2] at e
  have e3 := congrFun (congrFun e i) j
  have hmem : ((Ideal.absNorm I : ℕ) : Formalism.L2.Herm.intAf F E) ∈ idS F I := by
    rw [← map_natCast (oToS F E)]
    exact Ideal.mem_map_of_mem _ (Ideal.absNorm_mem I)
  have e4 : ((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) - 1) i j = ((Ideal.absNorm I : ℕ) : Formalism.L2.Herm.intAf F E) * ⟨z i j, hz i j⟩ := by
    apply Subtype.ext
    refine Eq.trans ?_ (e3.trans ?_)
    · simp only [Matrix.sub_apply, Matrix.one_apply]
      split_ifs <;> rfl
    · simp [nsmul_eq_mul]
  rw [e4]
  exact Ideal.mul_mem_right _ _ hmem

theorem princ_isOpen (N : GlobalTheory.Grid.Node D) {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) :
    IsOpen (((N.princ I).comap (Lev.finE N.V) : Subgroup (GA D N.V)) : Set (GA D N.V)) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig N.V.gram
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig N.V.gram
  have hf : Continuous (finHom N.V) := (continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ
  have hN : Ideal.absNorm I ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 hI
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ N.V N.β ∅,
    GlobalTheory.FunObj.eventually_cong_mat N.β hN hf (map_one _)] with κ ⟨h1, h2, _⟩ ⟨z, hz, e⟩
  exact ⟨h1, mem_princGL_of_cong h2 hz e⟩

theorem princ_isCompact (N : GlobalTheory.Grid.Node D) {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) :
    IsCompact ((Lev.levA N.V (N.princ I) : Subgroup (GA D N.V)) : Set (GA D N.V)) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig N.V.gram
  obtain ⟨C, hC, hCm⟩ := GlobalTheory.ParahoricCompact.exists_compact N.V N.β
  refine hC.of_isClosed_subset ((GlobalTheory.Ker.CongTop.isClosed_GfC N.V).inter
    (Subgroup.isClosed_of_isOpen _ (princ_isOpen N hI))) fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Lev.mem_levA.1 hk
  exact hCm k hk1 (GlobalTheory.Grid.princGL_top N.β ▸ GlobalTheory.Grid.princGL_mono N.β le_top hk2.2)

theorem exists_isMeasFD (V : HSp D) (hV : V.SigOK) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (ho : IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)))
    (hc : IsCompact ((Lev.levA V K : Subgroup (GA D V)) : Set (GA D V))) : ∃ μ 𝓕, Lev.IsMeasFD V K μ 𝓕 := by
  choose m hm using GlobalTheory.MinfMeasure.exists_isMinf
  obtain ⟨μ, hμ⟩ := GlobalTheory.LevelMeasure.exists_isMeasLevW D V hV K ho hc (fun _ m => Lev.IsMinf m) (fun _ => m _ _)
    (fun _ => (hm _ _).1) (fun _ => hm _ _) fun _ _ h => GlobalTheory.LevelMeasure.isMinf_unique (hm _ _) h
  obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D V μ hμ.1
  exact ⟨μ, 𝓕, hμ, h𝓕⟩

theorem exists_measDat (N : GlobalTheory.Grid.Node D) (hs : N.V.SigOK) (df : Prop) (hdf : df → ∀ τ, (N.V.sig τ).2 = 0)
    {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) : ∃ m : N.MeasDat, m.Is df (N.princ I) := by
  have ho := princ_isOpen N hI
  have hc := princ_isCompact N hI
  by_cases h : df
  · obtain ⟨μ, 𝓕, e⟩ := GlobalTheory.FunObj.exists_meas N.V hs (hdf h) (N.princ I) ⟨ho, hc⟩
    rw [if_pos rfl] at e
    exact ⟨⟨μ, 𝓕⟩, by unfold GlobalTheory.Grid.Node.MeasDat.Is; exact ⟨fun _ => e, fun hn => absurd h hn⟩⟩
  · obtain ⟨μ, 𝓕, e⟩ := exists_isMeasFD N.V hs _ ho hc
    exact ⟨⟨μ, 𝓕⟩, by unfold GlobalTheory.Grid.Node.MeasDat.Is; exact ⟨fun h' => absurd h' h, fun _ => e⟩⟩

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem exists_isMeas (G : GlobalTheory.Grid.GridPre R) (hS : G.IsSpaces) :
    ∃ m00 mV mP mX, (withMeas G m00 mV mP mX).IsMeas := by
  have hlvl : G.lvl R ≠ ⊥ := G.toPlaceDat.ideal_ne_bot R.Pg
  have htop : (⊤ : Ideal (𝓞 D.host.E)) ≠ ⊥ := top_ne_bot
  obtain ⟨m00, h00⟩ := exists_measDat (G.V 0 0) (D.sp.Y_sig 0) False (fun h => h.elim) hlvl
  have hV : ∀ i j, ∃ m : (G.nV i j).MeasDat, i + 1 ≤ D.R.m → j ≤ D.R.m →
      m.Is (if j = 0 then False else D.R.m - 1 ≤ j) ((G.nV i j).princ (if j = 0 then G.lvl R else ⊤)) := by
    intro i j
    by_cases h : i + 1 ≤ D.R.m ∧ j ≤ D.R.m
    · have hN := hS.vert i j h.1 h.2
      obtain ⟨m, hm⟩ := exists_measDat (G.nV i j) hN.sigOK (if j = 0 then False else D.R.m - 1 ≤ j)
        (fun hd τ => by
          rw [hN.sig τ]
          show (D.R.m - j) / 2 = 0
          by_cases hj : j = 0
          · rw [if_pos hj] at hd; exact hd.elim
          · rw [if_neg hj] at hd; omega)
        (I := if j = 0 then G.lvl R else ⊤) (by split_ifs; exacts [hlvl, htop])
      exact ⟨m, fun _ _ => hm⟩
    · exact ⟨⟨0, ∅⟩, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  have hP : ∀ i, ∃ m : (G.P i).MeasDat, i ≤ D.R.m → m.Is (i = D.R.m) ((G.P i).princ (G.lvl R)) := by
    intro i
    by_cases h : i ≤ D.R.m
    · have hN := hS.P i h
      obtain ⟨m, hm⟩ := exists_measDat (G.P i) hN.sigOK (i = D.R.m)
        (fun hd τ => by
          rw [hN.sig τ]
          show (D.R.m - i + 1) / 2 = 0
          omega) hlvl
      exact ⟨m, fun _ => hm⟩
    · exact ⟨⟨0, ∅⟩, fun h1 => absurd h1 h⟩
  have hX : ∀ j, ∃ m : (G.nX j).MeasDat, j + 1 ≤ D.R.m → m.Is True ((G.nX j).princ ⊤) := by
    intro j
    by_cases h : j + 1 ≤ D.R.m
    · have hN := hS.X j h
      obtain ⟨m, hm⟩ := exists_measDat (G.nX j) hN.sigOK True
        (fun _ τ => by
          rw [hN.sig τ]) htop
      exact ⟨m, fun _ => hm⟩
    · exact ⟨⟨0, ∅⟩, fun h1 => absurd h1 h⟩
  choose mV hmV using hV
  choose mP hmP using hP
  choose mX hmX using hX
  refine ⟨m00, mV, mP, mX, ⟨fun i hi => ?_, fun i j hi hj => ?_, fun i hi => hmP i hi, fun j hj => hmX j hj⟩⟩
  · cases i with
    | zero => exact h00
    | succ i =>
      have := hmV i 0 hi (Nat.zero_le _)
      rw [if_pos rfl, if_pos rfl] at this
      exact this
  · have := hmV i (j + 1) hi hj
    rw [if_neg (Nat.succ_ne_zero j), if_neg (Nat.succ_ne_zero j)] at this
    exact this

end GlobalTheory.GridJoin
