import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitOfUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralDefiniteQuotientEqClassSumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousFinGL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousPhiPrV
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsTransportAdelicCorrection
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartNonempty
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
import Formalism.LocalRingCardinality.PosOfIsomEmb

noncomputable section

namespace GlobalTheory.StepZeroNorm

section Chi

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {gp : Fin 2 → ℕ}

theorem eventually_chi {S : StepLevel F E σ J T f bad} {G : GLoc F E σ gp} {a t nb skip fc : ℕ} {zl : Bool}
    (L : GLev S G a t nb skip fc zl) (hgp : ∀ a, gp a ≠ 0) :
    letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    ∀ᶠ x : UPts σ J (FiniteAdeleRing (𝓞 F) F) in nhds 1, ∃ hx : x.1 ∈ S.U, S.chi ⟨x.1, hx⟩ = 1 := by
  letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  haveI := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
  have hfin : ∀ a, {v : HeightOneSpectrum (𝓞 F) | (gp a : 𝓞 F) ∈ v.asIdeal}.Finite := fun a => by
    have h0 : Ideal.span {(gp a : 𝓞 F)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.2 (hgp a)
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  have h1 : ∀ᶠ x : UPts σ J (FiniteAdeleRing (𝓞 F) F) in nhds 1, x.1 ∈ S.U := S.U_open.mem_nhds S.U.one_mem
  have hone : ∀ a v h, G.mat a v h (L.fr a v h) (bc (prV (E := E) v) (1 : UPts σ J (FiniteAdeleRing (𝓞 F) F)).1) = 1 := by
    intro a v h
    simp [GLoc.mat]
  have h2 : ∀ᶠ x : UPts σ J (FiniteAdeleRing (𝓞 F) F) in nhds 1, ∀ a : Fin 2, ∀ v ∈ {v : HeightOneSpectrum (𝓞 F) | (gp a : 𝓞 F) ∈ v.asIdeal},
      ∀ h : (gp a : 𝓞 F) ∈ v.asIdeal, redM F v (G.mat a v h (L.fr a v h) (bc (prV (E := E) v) x.1)) = 1 := by
    refine Filter.eventually_all.2 fun a => (Filter.eventually_all_finite (hfin a)).2 fun v h => ?_
    have hc : Continuous fun x : UPts σ J (FiniteAdeleRing (𝓞 F) F) => G.mat a v h (L.fr a v h) (bc (prV (E := E) v) x.1) := by
      have c0 : Continuous fun x : UPts σ J (FiniteAdeleRing (𝓞 F) F) => (x.1.val).map ((G.phi a v h).comp (prV (E := E) v)) :=
        (Units.continuous_val.comp continuous_subtype_val).matrix_map (GlobalTheory.LevelCharOpen.continuous_phi_prV G a v h)
      exact ((continuous_const (y := ((L.fr a v h)⁻¹).val)).matrix_mul c0).matrix_mul (continuous_const (y := (L.fr a v h).val))
    have h3 : ∀ᶠ x : UPts σ J (FiniteAdeleRing (𝓞 F) F) in nhds 1, ∀ i j,
        Valued.v (G.mat a v h (L.fr a v h) (bc (prV (E := E) v) x.1) i j - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) < 1 := by
      refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
      have c1 : Continuous fun x : UPts σ J (FiniteAdeleRing (𝓞 F) F) =>
          G.mat a v h (L.fr a v h) (bc (prV (E := E) v) x.1) i j - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j :=
        (hc.matrix_elem i j).sub continuous_const
      have ho : IsOpen {y : v.adicCompletion F | Valued.v y < 1} := by
        simpa using Valued.isOpen_ball (v.adicCompletion F) 1
      refine (ho.preimage c1).mem_nhds ?_
      rw [Set.mem_preimage, Set.mem_setOf_eq, hone, sub_self, map_zero]
      exact zero_lt_one
    exact h3.mono fun x hx _ => GlobalTheory.LevelCharOpen.redM_eq_one v _ hx
  filter_upwards [h1, h2] with x hx hr
  refine ⟨hx, Units.ext ?_⟩
  have hr1 : ∀ a v h, redM F v (G.mat a v h (L.fr a v h) (bc (prV (E := E) v) (1 : S.U).1)) = 1 := fun a v h =>
    GlobalTheory.LevelCharOpen.redM_eq_one v _ fun i j => by
      have := hone a v h
      simp only [OneMemClass.coe_one] at this ⊢
      rw [this, sub_self, map_zero]
      exact zero_lt_one
  rw [← map_one S.chi, L.chi_eq, L.chi_eq]
  refine Finset.prod_congr rfl fun a _ => finprod_congr fun v => finprod_congr fun h => ?_
  rw [hr a v h h, hr1]

end Chi

section Gen

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_open {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) {J : Matrix (Fin n) (Fin n) D.host.E}
    (hJ : J = V.gram.reindex (finCongr hn) (finCongr hn)) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    {S : StepLevel D.host.F D.host.E (sigD D) J T f bad} {G : GLoc D.host.F D.host.E (sigD D) D.host.g} {a t nb skip fc : ℕ} {zl : Bool}
    (L : GLev S G a t nb skip fc zl) :
    ∃ W : Subgroup (GA D V), IsOpen (W : Set (GA D V)) ∧ ∀ k ∈ W, k ∈ GfC V → ∀ κ : S.U, κ.1.1 = finM V hn k → S.chi κ = 1 := by
  subst hn
  subst hJ
  letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hev := eventually_chi L fun a => (D.host.g_prime a).ne_zero
  let φ : GA D V →* GL (Fin V.rank) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    (bc (toEAf D)).comp (matHom V)
  have hφ : ∀ g, (φ g).1 = finM V rfl g := fun g => RdLaw.finGL_val V g
  have hmem : ∀ g, φ g ∈ UPts (sigD D) (V.gram.reindex (finCongr rfl) (finCongr rfl)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := fun g => by
    obtain ⟨x, hx⟩ := RdVal.finM_mem V rfl _ rfl g
    have e : φ g = x.1 := Units.ext (by rw [hφ, hx])
    rw [e]; exact x.2
  have hc : Continuous fun g => (⟨φ g, hmem g⟩ : UPts (sigD D) (V.gram.reindex (finCongr rfl) (finCongr rfl)) _) :=
    (RdLaw.continuous_finGL V).subtype_mk _
  refine ⟨(S.chi.ker.map S.U.subtype).comap φ, Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_, ?_⟩
  · have e1 : (⟨φ 1, hmem 1⟩ : UPts (sigD D) (V.gram.reindex (finCongr rfl) (finCongr rfl)) _) = 1 := Subtype.ext (map_one φ)
    have ht := hc.tendsto' 1 1 e1
    refine (ht.eventually hev).mono ?_
    rintro g ⟨hx, h1⟩
    exact ⟨⟨φ g, hx⟩, h1, rfl⟩
  · rintro k ⟨κ', h1, e⟩ - κ hκ
    have : κ = κ' := Subtype.ext (Units.ext (by rw [hκ, ← hφ, ← e]; rfl))
    rw [this]
    exact h1

set_option maxHeartbeats 2000000 in

theorem card_stab {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) {J : Matrix (Fin n) (Fin n) D.host.E}
    (hJ : J = V.gram.reindex (finCongr hn) (finCongr hn)) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) (y : UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    {Γ : Type} [Group Γ] (i : Γ →* UJ (sigD D : D.host.E →+* D.host.E) J) (hi : Function.Injective i)
    (hr : ∀ γ : UJ (sigD D : D.host.E →+* D.host.E) J, γ ∈ i.range ↔
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 ∈ S.U.map (MulAut.conj y.1).toMonoidHom) :
    Nat.card {γ : GQ V // ∃ κ : S.U, finM V hn γ.1 * y.1.1 = y.1.1 * κ.1.1} = Nat.card Γ := by
  subst hn
  subst hJ
  have hinj : Function.Injective (incA D) :=
    Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)
  have hm : ∀ δ : UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr rfl) (finCongr rfl)),
      bc (incA D) δ.1 ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := fun δ => by
    have hδ' : cT (sigD D : D.host.E →+* D.host.E) δ.1.1 * V.gram * δ.1.1 = V.gram := δ.2
    have h2 := congrArg (fun M => M.map (incA D)) hδ'
    simp only [Matrix.map_mul] at h2
    exact h2
  let e : UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr rfl) (finCongr rfl)) → GQ V := fun δ =>
    ⟨⟨bc (incA D) δ.1, hm δ⟩, Subgroup.mem_subgroupOf.2 ⟨δ.1, δ.2, rfl⟩⟩
  have he : ∀ δ, finM V rfl (e δ).1 = (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ.1).1 := fun δ =>
    RdLaw.rat_finM V δ.1 _ rfl
  have key : ∀ δ, (∃ κ : S.U, finM V rfl (e δ).1 * y.1.1 = y.1.1 * κ.1.1) ↔ δ ∈ i.range := fun δ => by
    rw [hr, he]
    generalize bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ.1 = x
    constructor
    · rintro ⟨κ, hκ⟩
      have h1 : x * y.1 = y.1 * κ.1 := Units.ext hκ
      exact ⟨κ.1, κ.2, (mul_inv_eq_of_eq_mul h1.symm)⟩
    · rintro ⟨κ, hκ, h1⟩
      have h2 : y.1 * κ * y.1⁻¹ = x := h1
      exact ⟨⟨κ, hκ⟩, congrArg Units.val (eq_mul_of_mul_inv_eq h2).symm⟩
  refine (Nat.card_eq_of_bijective (fun s : Γ => (⟨e (i s), (key _).2 ⟨s, rfl⟩⟩ :
    {γ : GQ V // ∃ κ : S.U, finM V rfl γ.1 * y.1.1 = y.1.1 * κ.1.1})) ⟨fun s s' h => hi ?_, ?_⟩).symm
  · have h1 : (i s).1.1.map (incA D) = (i s').1.1.map (incA D) := congrArg (fun z => z.1.1.1.1) h
    exact Subtype.ext (Units.ext (Matrix.map_injective hinj h1))
  · rintro ⟨γ, hγ⟩
    obtain ⟨δ, hδ, e'⟩ := Subgroup.mem_subgroupOf.1 γ.2
    have h1 : e ⟨δ, hδ⟩ = γ := Subtype.ext (Subtype.ext e')
    obtain ⟨s, hs⟩ := (key ⟨δ, hδ⟩).1 (h1 ▸ hγ)
    exact ⟨s, Subtype.ext (by simp only [hs, h1])⟩

set_option maxHeartbeats 2000000 in

theorem integral_rdS {D : D7} (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) {n : ℕ} (hn : V.rank = n) {J : Matrix (Fin n) (Fin n) D.host.E}
    (hJ : J = V.gram.reindex (finCongr hn) (finCongr hn)) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) {cl : Type} [Fintype cl]
    (yc : cl → UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hb : Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S))) (hS : V.SigOK) (hP : V.IsPosDef)
    (hχ : ∀ κ : S.U, ‖(S.chi κ : ℂ)‖ = 1)
    (hW : ∃ W : Subgroup (GA D V), IsOpen (W : Set (GA D V)) ∧ ∀ k ∈ W, k ∈ GfC V → ∀ κ : S.U, κ.1.1 = finM V hn k → S.chi κ = 1)
    (lam : D.what₂.Tau → DomWeight n) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (y : Frames (gramC J (embT D))) :
    ∃ c : ℝ, 0 < c ∧ ∀ ip : cl → (Frames (gramC J (embT D)) → ℂ) → (Frames (gramC J (embT D)) → ℂ) → ℂ,
      (∀ a, GlobalTheory.ValSchur.IsFock _ lam (ip a) ∧ GlobalTheory.ValSchur.IsSesq (ip a)) →
      ∀ φ ∈ FiC S (embT D) lam yc, ∀ ψ ∈ FiC S (embT D) lam yc,
        ∫ g in 𝓕, rdS θ V hn S yc φ y g * star (rdS θ V hn S yc ψ y g) ∂μ =
          (c : ℂ) * ∑ a, ((Nat.card {γ : GQ V // ∃ κ : S.U, finM V hn γ.1 * (yc a).1.1 = (yc a).1.1 * κ.1.1} : ℕ) : ℂ)⁻¹ *
            ip a (ψ a) (φ a) := by
  subst hn
  subst hJ
  have hPD : ∀ τ, (gramAt D V τ).PosDef := fun τ => by
    have := hS (tauE D τ)
    rw [hP] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  choose h hh1 hh2 using fun a => GlobalTheory.Core.Mi.PinModel.exists_finM V rfl (yc a)
  obtain ⟨vol, ν, hvol, hν, -, hsum⟩ := GlobalTheory.T.integral_definiteQuotient_eq_classSum D θ hθ V _ rfl _ rfl T f bad S cl yc hb hS hPD μ 𝓕 hμ h𝓕 h
    fun a => ⟨hh1 a, hh2 a⟩
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : T2Space (GA D V) := by
    have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
    first | exact hT.1 | exact hT.2.1 | exact hT.2.2.1 | exact hT.2.2.2.1 | exact hT.2.2.2.2.1 | exact hT.2.2.2.2.2.1 | exact hT.2.2.2.2.2.2
  haveI : CompactSpace (GinfC V) := isCompact_iff_compactSpace.1 (Formalism.IndefR.Eqv.isCompact_GinfC hS fun τ => Or.inl (hP τ))
  haveI : BorelSpace (GinfC V) := Subtype.borelSpace _
  have hone : ∀ τ, infM θ V rfl 1 τ = 1 := RdLaw.infM_fin θ V 1 (one_mem _)
  have hu : ∀ (k : GinfC V) τ, IsUnit (infM θ V rfl k.1 τ).det := fun k τ =>
    Matrix.isUnit_det_of_right_inverse (B := infM θ V rfl k.1⁻¹ τ) (by rw [← RdLaw.infM_mul, mul_inv_cancel, hone])
  obtain ⟨c, hc, havg⟩ := GlobalTheory.ValSchur.avg_eq (G := gramC (V.gram.reindex (finCongr rfl) (finCongr rfl)) (embT D)) hPD lam ν
    (fun k : GinfC V => infM θ V rfl k.1) hu (fun τ => (RdLaw.continuous_infM θ hθ V τ).comp continuous_subtype_val)
    (fun a b τ => RdLaw.infM_mul θ V a.1 b.1 τ) (fun g hg => by
      obtain ⟨k, hk, e⟩ := (GlobalTheory.SmoothForms.RealPts.glue θ hθ V).2 g hg
      exact ⟨⟨k, hk⟩, fun τ => (RdLaw.infM_rfl θ V k τ).trans (e τ)⟩) y
  refine ⟨vol * c, mul_pos hvol hc, fun ip hip φ hφ ψ hψ => ?_⟩
  have L1 := RdLaw.rdS_laws D θ hθ V _ rfl _ rfl T f bad S cl yc hb lam φ hφ y
  have L2 := RdLaw.rdS_laws D θ hθ V _ rfl _ rfl T f bad S cl yc hb lam ψ hψ y
  have hval : ∀ φ ∈ FiC S (embT D) lam yc, ∀ a, φ a ∈ ValC _ lam ∧ ∀ k : GinfC V,
      rdS θ V rfl S yc φ y (h a * k.1) = φ a (Frames.tr (infM θ V rfl k.1) (hu k) y) := by
    rintro _ ⟨Φ, hΦ, rfl⟩ a
    refine ⟨(Submodule.mem_inf.1 hΦ).2 (yc a) (Set.mem_univ _), fun k => ?_⟩
    refine (GlobalTheory.AdForm.rdS_val D θ hθ V _ rfl _ rfl T f bad S cl yc hb Φ (Submodule.mem_inf.1 hΦ).1 y (h a * k.1)).2.2
      (yc a) _ ?_ fun τ => ?_
    · rw [RdLaw.finM_mul, RdLaw.finM_inf V k.1 k.2, Matrix.mul_one, hh2]
    · rw [RdLaw.infM_mul, RdLaw.infM_fin θ V _ (hh1 a), Matrix.one_mul]
      rfl
  refine (hsum (fun g => rdS θ V rfl S yc φ y g * star (rdS θ V rfl S yc ψ y g)) ((L1.2.2.2 hW).mul (L2.2.2.2 hW).star)
    (fun γ hγ x => by simp only [L1.1 γ hγ, L2.1 γ hγ]) ?_).trans ?_
  swap
  · rw [Complex.ofReal_mul, mul_assoc, Finset.mul_sum (a := (c : ℂ))]
    refine congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
    simp only [(hval φ hφ a).2, (hval ψ hψ a).2]
    rw [havg _ (hip a).1 (hip a).2 _ (hval ψ hψ a).1 _ (hval φ hφ a).1]
    ring
  · rintro k hk ⟨κ, hκ⟩ x
    have h1 : (S.chi κ : ℂ) * star (S.chi κ : ℂ) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ]; simp
    simp only [L1.2.1 k hk κ hκ, L2.2.1 k hk κ hκ, star_mul']
    linear_combination (rdS θ V rfl S yc φ y x * star (rdS θ V rfl S yc ψ y x)) * h1

end Gen

end GlobalTheory.StepZeroNorm

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000 in

theorem GlobalTheory.StepZeroNorm.integral_rd_eq_inner : ∀ (D : D7) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (θ : InfFam D), IsInfFam θ → CoCpt (D.sp.X 0) → ∀ (vS : Vol (D.sp.X 0)) (y : (D.mem u).C.Y 0), ∃ c : ℝ, 0 < c ∧ ∀ φ ψ : D.what₂.Mu u, ∫ g in vS.𝓕, (GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u φ).1 y g * star ((GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u ψ).1 y g) ∂vS.μ = (c : ℂ) * inner ℂ ψ φ := by
  intro D u F θ hθ _ vS y
  obtain ⟨c, hc, H⟩ := GlobalTheory.StepZeroNorm.integral_rdS θ hθ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) rfl F.cls0.lev
    F.cls0.y F.cls0.y_bij (D.sp.X_sig 0) (D7.X_posDef D 0 (Nat.zero_le _)) F.glev0.chi_unit
    (GlobalTheory.StepZeroNorm.exists_open _ _ rfl F.glev0) (Formalism.L2.Forms.lamT u 0) vS.μ vS.𝓕 vS.haar vS.fund (F.val0.eY y)
  refine ⟨c, hc, fun φ ψ => ?_⟩
  have hm : ∀ φ : D.what₂.Mu u, (fun a z => (D.eMu u φ).1 a (F.val0.eY.symm z)) ∈
      Formalism.L2.Forms.FiC F.cls0.lev (Formalism.L2.Forms.embT D) (Formalism.L2.Forms.lamT u 0) F.cls0.y := fun φ =>
    (F.val0.Fi _).1 (by rw [(D.fm u).Fi_zero]; exact (D.eMu u φ).2.1)
  have h1 := H (fun a f g => (D.fm u).ipV 0 a (fun z => f (F.val0.eY z)) (fun z => g (F.val0.eY z))) (fun a => ⟨?_, ?_, ?_⟩)
    _ (hm φ) _ (hm ψ)
  · refine h1.trans (congrArg _ ?_)
    rw [D.eMu_isom, MemberForms.ipC]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [GlobalTheory.StepZeroNorm.card_stab _ _ rfl F.cls0.lev (F.cls0.y a) (F.cls0.stabI a) (F.cls0.stabI_inj a) (F.cls0.stabI_range a)]
    simp only [Equiv.symm_apply_apply]
    rfl
  · intro o ho P hP Q hQ
    have h2 := F.val0.ipV a o ho P (Formalism.L2.Forms.lamT_zero u ▸ hP) Q (Formalism.L2.Forms.lamT_zero u ▸ hQ)
    rw [← Formalism.L2.Forms.lamT_zero u] at h2
    exact h2
  · intro z f f' g
    have e : (fun x => (z • f + f') (F.val0.eY x)) = z • (fun x => f (F.val0.eY x)) + fun x => f' (F.val0.eY x) := rfl
    simp only [e, map_add, LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
  · intro z f g g'
    have e : (fun x => (z • g + g') (F.val0.eY x)) = z • (fun x => g (F.val0.eY x)) + fun x => g' (F.val0.eY x) := rfl
    simp only [e, map_add, map_smul, smul_eq_mul]
