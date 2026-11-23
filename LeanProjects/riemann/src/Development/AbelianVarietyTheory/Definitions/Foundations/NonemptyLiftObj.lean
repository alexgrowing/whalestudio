import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFixedOfContract
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DatumCurveIntegralUnitDiscModel

noncomputable section
namespace GlobalTheory.Glob.IntegralWittCoefficients.Model
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

theorem eisG_scale {Λ Λ' : AddSubgroup ℂ} {c : ℂ} (hc : c ≠ 0) (h : ∀ z, z ∈ Λ' ↔ c * z ∈ Λ) (k : ℕ) :
    eisG Λ' k = c ^ (2 * k) * eisG Λ k := by
  let e : {w : ℂ // w ∈ Λ' ∧ w ≠ 0} ≃ {w : ℂ // w ∈ Λ ∧ w ≠ 0} :=
    Equiv.subtypeEquiv (Equiv.mulLeft₀ c hc) (fun w => by simp [h, hc])
  unfold eisG
  rw [← e.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun w => ?_
  have hw : (w : ℂ) ≠ 0 := w.2.2
  have : ((e w : {w : ℂ // w ∈ Λ ∧ w ≠ 0}) : ℂ) = c * w := rfl
  rw [this]
  field_simp
  ring

def gaussPair : PeriodPair := ⟨1, Complex.I, by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have e1 := congrArg Complex.re h
  have e2 := congrArg Complex.im h
  simp at e1 e2
  exact ⟨e1, e2⟩⟩

theorem exists_gauss : ∃ (Λ : AddSubgroup ℂ) (c : ℂ), c ≠ 0 ∧
    (∀ z, z ∈ Λ ↔ ∃ m n : ℤ, (m : ℂ) + n * Complex.I = c * z) ∧ g2 Λ = 4 ∧ g3 Λ = 0 := by
  let Λ₀ : AddSubgroup ℂ := gaussPair.lattice.toAddSubgroup
  have hm : ∀ z, z ∈ Λ₀ ↔ ∃ m n : ℤ, (m : ℂ) + n * Complex.I = z := fun z => by
    show z ∈ gaussPair.lattice ↔ _
    rw [PeriodPair.mem_lattice]
    simp [gaussPair]
  have hI : ∀ z, z ∈ Λ₀ ↔ Complex.I * z ∈ Λ₀ := fun z => by
    rw [hm, hm]
    constructor
    · rintro ⟨m, n, rfl⟩
      refine ⟨-n, m, ?_⟩
      push_cast
      linear_combination (-(n : ℂ)) * Complex.I_mul_I
    · rintro ⟨m, n, h⟩
      refine ⟨n, -m, ?_⟩
      push_cast
      linear_combination (-Complex.I) * h + ((n : ℂ) - z) * Complex.I_mul_I
  have h3 : eisG Λ₀ 3 = 0 := by
    have := eisG_scale Complex.I_ne_zero hI 3
    have h6 : Complex.I ^ (2 * 3) = -1 := by rw [pow_mul, Complex.I_sq]; norm_num
    rw [h6] at this
    linear_combination this / 2
  have hd := GlobalTheory.CurveLattice.discr_ne_zero Λ₀ gaussPair (fun _ => Iff.rfl)
  have h2 : g2 Λ₀ ≠ 0 := by
    intro h0
    apply hd
    simp [TaylorLogMetric.discr, h0, g3, h3]
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (4 / g2 Λ₀) (n := 4) (by norm_num)
  have hc0 : c ≠ 0 := by
    rintro rfl
    have : (4 : ℂ) / g2 Λ₀ ≠ 0 := div_ne_zero (by norm_num) h2
    apply this; rw [← hc]; norm_num
  let Λ : AddSubgroup ℂ := Λ₀.comap (AddMonoidHom.mulLeft c)
  have hΛ : ∀ z, z ∈ Λ ↔ c * z ∈ Λ₀ := fun _ => Iff.rfl
  refine ⟨Λ, c, hc0, fun z => (hΛ z).trans (hm _), ?_, ?_⟩
  · have : g2 Λ = c ^ 4 * g2 Λ₀ := by
      rw [g2, g2, eisG_scale hc0 hΛ 2]; ring
    rw [this, hc]; field_simp
  · rw [g3, eisG_scale hc0 hΛ 3, h3]; simp

theorem nonempty_place (p : ℕ) [Fact p.Prime] : Nonempty (Qbar →+* ℂ_[p]) :=
  haveI : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  ⟨(IsAlgClosed.lift (R := ℚ) (S := Qbar) (M := ℂ_[p])).toRingHom⟩

theorem norm_two {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by
  have h1 : (2 : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] ((2 : ℕ) : ℚ_[p]) := by simp [map_ofNat]
  rw [h1, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.coprime_primes Fact.out Nat.prime_two).2 hp

theorem exists_ok (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    ∃ g : G1 p, g.Ok ∧ ModelOverW g.lam g.abelian₂ g.C ∧ g.W = ⟨0, 0, 0, -1, 0⟩ ∧ g2 g.abelian₂ = 4 ∧ g3 g.abelian₂ = 0 ∧
      ∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ g.abelian₂ ↔ ∃ m n : ℤ, (m : ℂ) + n * Complex.I = c * z := by
  obtain ⟨Λ, c, hc, hΛ, h2, h3⟩ := exists_gauss
  obtain ⟨lam⟩ := nonempty_place p
  have hW : (1 : WeierstrassCurve.VariableChange ℂ_[p]) • wModel lam Λ = ⟨0, 0, 0, -1, 0⟩ := by
    rw [one_smul, wModel, h2, h3]
    have e1 : lamC lam (-4 / 4) = -1 := by
      have : (-4 / 4 : ℂ) = ((-1 : Qbar) : ℂ) := by norm_num
      rw [this, lamC, dif_pos (-1 : Qbar).2]
      exact (map_neg lam 1).trans (by rw [map_one])
    have e0 : lamC lam (-0 / 4) = 0 := by
      have : (-0 / 4 : ℂ) = ((0 : Qbar) : ℂ) := by norm_num
      rw [this, lamC, dif_pos (0 : Qbar).2]
      exact map_zero lam
    rw [e1, e0]
  obtain ⟨wq, hwq⟩ := GlobalTheory.GenusOneDatum.exists_isWq ((1 : WeierstrassCurve.VariableChange ℂ_[p]) • wModel lam Λ)
  obtain ⟨ex, he0, he⟩ := GlobalTheory.GenusOneDatum.exists_subst_eq_X _ (GlobalTheory.GenusOneDatum.constantCoeff_flog _ wq)
    (GlobalTheory.GenusOneDatum.coeff_one_flog hwq)
  refine ⟨⟨lam, Λ, 1, wq, ex⟩, ⟨?_, hwq, he0, he⟩, ?_, hW, h2, h3, c, hc, hΛ⟩
  · simp only [IsModelU, hW, IsIntP]
    refine ⟨by simp, by simp, by simp, by simp, by simp, ?_⟩
    have : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℂ_[p]).Δ = 2 ^ 6 := by
      simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      norm_num
    rw [this, norm_pow, norm_two hp, one_pow]
  · simp only [ModelOverW, hW]
    exact ⟨zero_mem _, zero_mem _, zero_mem _, neg_mem (one_mem _), zero_mem _⟩

def ofRec {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) : G1 p := ⟨g.lam, g.abelian₂, g.C, g.wq, g.ex⟩

theorem at_ofRec (D : D7) {p : ℕ} [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p) :
    At D cc δ (ofRec g) ↔ GL3Theta.At D cc δ g := Iff.rfl

theorem exists_at (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (cc : Ideal (𝓞 D.host.K))
    (h1 : IsCurveIdeal D cc) (h3 : Nat.Coprime (Ideal.absNorm cc) p) :
    ∃ (δ : ℂ) (g : G1 p), At D cc δ g ∧ g.lam = lam := by
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (TaylorLogMetric.discr (lamOf D cc 1)) (n := 12) (by norm_num)
  obtain ⟨g, hg, hl, -⟩ := GlobalTheory.GenusOneDatum.exists_genusOne_datum D (GlobalTheory.UnitModel.modelEx_holds D) p lam cc δ
    ⟨h1, hδ⟩ h3
  exact ⟨δ, ofRec g, hg, hl⟩

theorem exists_at_top (D : D7) (p : ℕ) [Fact p.Prime] : ∃ (δ : ℂ) (g : G1 p), At D ⊤ δ g := by
  obtain ⟨lam⟩ := nonempty_place p
  obtain ⟨δ, g, h, -⟩ := exists_at D p lam ⊤ ⟨by simp, by simp⟩ (by simp)
  exact ⟨δ, g, h⟩

theorem simeq_refl {σ : Type*} {p : ℕ} [Fact p.Prime] (f : MvPowerSeries σ ℂ_[p]) : Simeq f f := by
  refine ⟨by simp, fun α => ?_⟩
  rw [sub_self]
  show ‖∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α ((0 : MvPowerSeries σ ℂ_[p]) ^ n) / (n.factorial : ℂ_[p])‖ ≤ 1
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, MvPowerSeries.coeff_one]
    split_ifs <;> simp
  · intro n _ hn
    simp [hn]
  · simp

theorem not_simeq_X (p : ℕ) [Fact p.Prime] : ¬ Simeq (Xv () : MvPowerSeries Unit ℂ_[p]) 0 := by
  rintro ⟨-, h⟩
  have h1 := h (Finsupp.single () p)
  rw [sub_zero] at h1
  change ‖∑ n ∈ Finset.range (((Finsupp.single () p).sum fun _ k => k) + 1),
    MvPowerSeries.coeff (Finsupp.single () p) ((MvPowerSeries.X () : MvPowerSeries Unit ℂ_[p]) ^ n) /
      (n.factorial : ℂ_[p])‖ ≤ 1 at h1
  rw [Finset.sum_eq_single p] at h1
  · rw [MvPowerSeries.coeff_X_pow, if_pos rfl, norm_div, norm_one] at h1
    have e : ((p.factorial : ℕ) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] ((p.factorial : ℕ) : ℚ_[p]) := by simp
    have hlt : ‖((p.factorial : ℕ) : ℂ_[p])‖ < 1 := by
      rw [e, norm_algebraMap', Padic.norm_natCast_lt_one_iff]
      exact Nat.dvd_factorial (Fact.out : p.Prime).pos le_rfl
    have hpos : 0 < ‖((p.factorial : ℕ) : ℂ_[p])‖ := by
      rw [norm_pos_iff]; exact_mod_cast p.factorial_ne_zero
    rw [div_le_one hpos] at h1
    linarith
  · intro n _ hn
    rw [MvPowerSeries.coeff_X_pow, if_neg]
    · simp
    · intro e
      exact hn ((Finsupp.single_injective ()) e).symm
  · simp

theorem coeff_one_logF (p : ℕ) [Fact p.Prime] : PowerSeries.coeff 1 (logF p) = 1 := by
  have hp : (p : ℕ) ^ 2 ≠ 1 := by
    have := (Fact.out : p.Prime).two_le
    nlinarith
  simp [logF, Finset.sum_range_succ, hp.symm]

theorem hP_smul {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] (a : ℂ_[p] × ℂ_[p]) (x y : ι → ℂ_[p] × ℂ_[p]) :
    hP (fun k => a * x k) y = a * hP x y ∧ hP x (fun k => a * y k) = a.swap * hP x y := by
  constructor
  · simp [hP, Finset.mul_sum, mul_assoc]
  · simp only [hP, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ext <;> simp <;> ring

def stdLat (E : Type) [Field E] [NumberField E] (N : ℕ) : Submodule (𝓞 E) (Fin N → E) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)

theorem mem_range_iff {E : Type} [Field E] [NumberField E] (x : E) :
    x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x :=
  ⟨by rintro ⟨a, rfl⟩; exact a.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

theorem mem_stdLat {E : Type} [Field E] [NumberField E] {N : ℕ} (x : Fin N → E) :
    x ∈ stdLat E N ↔ ∀ k, IsIntegral ℤ (x k) := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]
  exact forall_congr' fun k => mem_range_iff (x k)

theorem isSDLat_std (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ) : IsSDLat E N (stdLat E N) := by
  have hs : ∀ k : Fin N, (Pi.single k 1 : Fin N → E) ∈ stdLat E N := fun k => by
    rw [mem_stdLat]
    intro j
    rw [Pi.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  refine ⟨Submodule.fg_pi fun _ => ?_, ?_, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin N)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨k, rfl⟩
    simpa using hs k
  · rw [mem_range_iff]
    rw [mem_stdLat] at hx hy
    exact IsIntegral.sum _ fun i _ => ((hx i).map (starRingEnd E).toIntAlgHom).mul (hy i)
  · rw [mem_stdLat]
    intro k
    have := h _ (hs k)
    rw [mem_range_iff] at this
    simpa [stdH, Pi.single_apply, apply_ite] using this

def frameChain (D : D7) (u : D.what₂.Word) : ColumnChain D.R D.what₂.Tau (D.hcW u) where
  cls _ := Unit
  clsFin _ := inferInstance
  stab _ _ := Unit
  stabGrp _ _ := inferInstance
  stabFin _ _ := inferInstance
  DGam := 1
  DGam_pos := one_pos
  dvd_DGam _ _ _ := by simp
  Y i := {f : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ // ∀ τ, (f τ).det ≠ 0}
  de _ y τ := (y.1 τ).det
  de_ne _ y τ := y.2 τ
  rhoDet _ _ := 1
  rhoDet' _ _ := 1
  rho_norm _ _ _ := norm_one
  rho'_norm _ _ _ := norm_one
  unf _ _ _ := 0
  sSharp := (D.mem u).C.sSharp
  sSharp_eq := (D.mem u).C.sSharp_eq
  sDiv := (D.mem u).C.sDiv
  sDiv_eq := (D.mem u).C.sDiv_eq

theorem nonempty_liftObj (D : D7) (u : D.what₂.Word) (s : D.what₂.Tau → ℂ)
    (hs : ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M), (∀ τ x, embT D τ x ∈ M) ∧ ∀ τ, ∃ t : M, (t : ℂ) = s τ ∧
      ellT D M τ = Submodule.span (𝓞 M) {t}) : Nonempty (LiftObj D (frameChain D u)) := by
  let _ := D.host.cmStar
  exact ⟨{
    mt := D.muTil
    L0 := fun i => ⟨stdLat _ _, isSDLat_std _ _⟩
    lattice_integral_coordinates := fun i x => mem_stdLat x
    lat := fun i _ => ⟨stdLat _ _, isSDLat_std _ _⟩
    dt := fun _ _ => 1
    dt_lat := fun i c => (D.relDet_self _ _).symm
    c13 := fun i _ => ⟨fun c => by simp [frameChain], fun c => by simp [frameChain]⟩
    frm := fun i y => y.1
    frm_inj := fun i _ => Subtype.val_injective
    frm_range := fun i _ f => ⟨by rintro ⟨y, rfl⟩; exact y.2, fun h => ⟨⟨f, h⟩, rfl⟩⟩
    frm_de := fun _ _ _ _ => rfl
    dgen := s
    dgen_gen := hs
    S := ∅
    Th := fun _ _ _ _ => 0 }⟩

end GlobalTheory.Glob.IntegralWittCoefficients.Model
