import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuotVolumeNeZeroNeTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
import Formalism.LocalRingCardinality.SpanPowerMembership.ExistsOmegaLeb
import Formalism.LocalRingCardinality.SpanPowerMembership.HaarDensityNeZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj

namespace GlobalTheory.FunObjModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem isMeasLevW_unique {V : HSp D} {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))} {good} {μ μ' : Measure (GA D V)}
    (hg : ∀ ρ m, good ρ m → m.IsHaarMeasure) (h : Lev.IsMeasLevW V K good μ) (h' : Lev.IsMeasLevW V K good μ') : μ = μ' := by
  obtain ⟨hloc, hsc, ht2, hbor, htg, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨hμ, ⟨θ, hθ⟩, hall⟩ := h
  obtain ⟨hμ', -, hall'⟩ := h'
  obtain ⟨⟨A, hA⟩, hallA⟩ := hall θ hθ
  obtain ⟨⟨m, hm⟩, hallm⟩ := hallA A hA
  have hvol := hallm m hm
  have hvol' := (hall' θ hθ).2 A hA |>.2 m hm

  choose C hC hC1 using fun ρ => exists_compact_mem_nhds (1 : Formalism.BasicNotions.UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2)
  have hB : ∀ ρ, MeasurableSet (interior (C ρ)) := fun ρ => isOpen_interior.measurableSet
  have hpos : ∀ ρ, m ρ (interior (C ρ)) ≠ 0 := fun ρ => by
    have := hg ρ (m ρ) (hm ρ)
    exact isOpen_interior.measure_ne_zero (m ρ) ⟨1, mem_interior_iff_mem_nhds.2 (hC1 ρ)⟩
  have hfin : ∀ ρ, m ρ (interior (C ρ)) ≠ ⊤ := fun ρ => by
    have := hg ρ (m ρ) (hm ρ)
    exact ((measure_mono interior_subset).trans_lt (hC ρ).measure_lt_top).ne
  have e1 := hvol (fun ρ => interior (C ρ)) hB
  have e2 := hvol' (fun ρ => interior (C ρ)) hB
  set P := ∏ ρ, m ρ (interior (C ρ)) with hPdef
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun ρ _ => hpos ρ
  have hPtop : P ≠ ⊤ := ENNReal.prod_ne_top fun ρ _ => hfin ρ
  have := hμ
  have := hμ'

  obtain ⟨c, hs⟩ : ∃ c : NNReal, μ' = c • μ := ⟨_, MeasureTheory.Measure.isMulLeftInvariant_eq_smul μ' μ⟩
  have e3 : ∀ s, μ' s = c * μ s := fun s => by
    simp only [hs, MeasureTheory.Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [e3, e1] at e2
  have hc1 : c = 1 := by exact_mod_cast (ENNReal.mul_eq_right hP0 hPtop).1 e2
  rw [hs, hc1, one_smul]

theorem isAt_unique {M M' : Vol G} {X : Node} {K} (h : M.IsAt X K) (h' : M'.IsAt X K) : M.ν X = M'.ν X := by
  unfold Vol.IsAt at h h'
  split_ifs at h h'
  · exact isMeasLevW_unique (fun _ _ hm => hm.1) h.1 h'.1
  · exact isMeasLevW_unique (fun _ _ hm => hm.1) h.1 h'.1

variable (W : G.Weil)

theorem liftA_indep {M M' : Vol G} (a : Arrow T) {K} (h : M.IsAt a.src K) (h' : M'.IsAt a.src K) (f : Sch G a) (F : Fn G a.src)
    (hinv : ∀ x, ∀ γ ∈ GQ (G.V a.src), ∀ g, W.kerA a f (γ * g) x * F (γ * g) = W.kerA a f g x * F g) :
    liftA W M a f F = liftA W M' a f F := by
  obtain ⟨hloc, hsc, ht2, hbor, htg, hdisc, hcount⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V a.src)
  have hν : M.ν a.src = M'.ν a.src := isAt_unique h h'
  obtain ⟨hH, hfd⟩ := h.haar_fund
  obtain ⟨-, hfd'⟩ := h'.haar_fund
  rw [← hν] at hfd'
  funext x
  rw [liftA_apply, liftA_apply, ← hν]
  exact hfd.setIntegral_eq hfd' fun γ y => hinv x γ γ.2 y

theorem embTop_hom : ∃ s : GA D (G.V (.top 0)) →* GA D (G.V (.grid D.R.m 0)), Continuous s ∧ embTop G = s ∧
    ∀ γ ∈ GQ (G.V (.top 0)), s γ ∈ GQ (G.V (.grid D.R.m 0)) := by
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  obtain ⟨s, hc, hrel, hrat⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D _ _ (G.rowDec 0 hm).ι (G.rowDec 0 hm).isom
  refine ⟨s, hc, ?_, hrat⟩
  funext h
  exact ((embRel_iff _ h (s h)).mp ((hrel h (s h)).mpr rfl)).symm

private theorem besChar_mul_eq_of_embRel {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι)
    (ψ : AddChar (AF D.host.F) ℂ) (g n : GA D B) (h : GA D A) (hrel : EmbRel B A ι g h) :
    besChar ψ d (n * g) = besChar ψ d n := by

  have key : ∀ x : Fin B.rank → D.host.E,
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A ι) * B.gram).mulVec x = 0 →
      (subOne B (n * g)).mulVec (ratV x) = (subOne B n).mulVec (ratV x) := by
    intro x hx
    have h2 : ((matHom B g).1 : Matrix _ _ _).mulVec (ratV x) = ratV x := hrel.2 x hx
    rw [subOne, subOne, map_mul, Units.val_mul, Matrix.sub_mulVec, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, h2]
  have hcol : ∀ i, (subOne B (n * g)).mulVec (ratV fun k => d.e k i) = (subOne B n).mulVec (ratV fun k => d.e k i) := by
    intro i
    apply key
    funext j
    have := congrFun (congrFun d.e_perp j) i
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  have hz := key d.z d.z_perpA
  have hP : IsBesVal ψ d (n * g) = IsBesVal ψ d n := by
    funext v
    simp only [IsBesVal, hcol, hz]
  unfold besChar
  rw [hP]

theorem exists_Bplus_ne_zero {M : Vol G} (hM : M.IsRow) : ∃ φ F, BplusConv W M φ F ∧ Bplus W M φ F ≠ 0 := by
  have hψ0 : ∀ x, W.ψ x ≠ 0 := fun x h0 => by
    have := W.ψ.map_add_eq_mul x (-x)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul] at this
    exact one_ne_zero this
  have hchi0 : ∀ g, besChar W.ψ G.besTop g ≠ 0 := by
    intro g
    unfold besChar
    split_ifs with hv
    · obtain ⟨a, b, -, -, hval⟩ := hv.choose_spec
      rw [hval]
      exact hψ0 _
    · exact one_ne_zero
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega

  have hfun : besInt W (fun _ => (1 : ℂ)) (fun g => (star (besChar W.ψ G.besTop g))⁻¹) = fun _ _ => 1 := by
    funext h n
    have hrel : EmbRel _ _ (G.rowDec 0 hm).ι (embTop G h) h := (embRel_iff (G.rowDec 0 hm) h (embTop G h)).mpr rfl
    simp only [besInt, one_mul]
    rw [besChar_mul_eq_of_embRel G.besTop W.ψ (embTop G h) (n : GA D _) h hrel]
    exact inv_mul_cancel₀ (star_ne_zero.2 (hchi0 _))
  obtain ⟨-, -, hN⟩ := hM.unip
  have hq := GlobalTheory.Mem.QuotVol.quot_volume_ne_zero_ne_top D _ (M.ν (.top 0)) (M.fd (.top 0)) hM.top.haar_fund
  refine ⟨fun _ => 1, fun g => (star (besChar W.ψ G.besTop g))⁻¹, ?_, ?_⟩
  · unfold BplusConv
    rw [hfun]
    refine ⟨fun h => integrableOn_const (by rw [hN]; simp), ?_⟩
    simp only [setIntegral_const, Measure.real, hN]
    exact integrableOn_const hq.2
  · unfold Bplus
    rw [hfun]
    simp [Measure.real, hN]
    exact ENNReal.toReal_ne_zero.2 hq

theorem tensT_single {X Y : Node} {p : Path T X Y} (P : PolT G p) (d : PureT G p) (c c' : ℂ) :
    tensT W (Finsupp.single P c) (Finsupp.single d c') =
      Finsupp.single (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P) (c * c') := by
  simp [tensT, Finsupp.sum_single_index]

theorem levJ_col (t : T) (j : ℕ) : levJ G t (.grid 0 (j + 1)) = levCol L t j := rfl

example (t : T) : (givenPath t 3).arrows = [.down t 0 2, .down t 0 1, .down t 0 0, .right 0 0, .right 1 0, .right 2 0] ∧
    (oppPath t 3).arrows = [.right 0 3, .right 1 3, .right 2 3, .down t 3 2, .down t 3 1, .down t 3 0] := ⟨rfl, rfl⟩

example (M : Vol G) (t : T) (f : ∀ j : Fin 2, Sch G (.down t 0 j)) (u : Fn G (.grid 0 2)) :
    liftP W M (downPath t 0 2) (downFam t 0 2 f) u = liftA W M (.down t 0 0) (f 0) (liftA W M (.down t 0 1) (f 1) u) := rfl

end GlobalTheory.FunObjModel

end
