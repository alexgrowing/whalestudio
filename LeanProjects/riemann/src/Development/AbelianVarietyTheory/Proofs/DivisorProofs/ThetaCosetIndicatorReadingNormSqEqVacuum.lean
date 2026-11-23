import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFinitePointReadsClassicalTranslation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexStandardInfSkewThetaLatticeEqAbsNormPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewIdealLatticePointRationalNormKills
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

namespace GlobalTheory.NormRatio.CosetNorm

open Formalism.MainNotions.TaylorLogMetric (VC tor0 La Iop U al YYl embV)
open Formalism.MainNotions.StandardLatticesGL3 (stdL pt La0 Wd wdPh Crv)

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem heisO_comm (x y : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T x (heisO ψ S T y f) = ψ (symplO S T x y) • heisO ψ S T y (heisO ψ S T x f) := by
  have e : symplO S T x y + symplOH S T y x = symplOH S T x y := by
    have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
      rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]; norm_num
    unfold symplOH
    rw [GlobalTheory.OrientedHeis.symplO_skew x y]
    linear_combination (-symplO S T x y) * h2
  rw [GlobalTheory.OrientedHeis.heisO_heisO, GlobalTheory.OrientedHeis.heisO_heisO, smul_smul, ← AddChar.map_add_eq_mul, e, add_comm]

theorem heisO_smul (x : WO S T) (c : ℂ) (f : WO S T → ℂ) : heisO ψ S T x (c • f) = c • heisO ψ S T x f := by
  funext w
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem ip_heisO_eq_zero {ΛS : Lat S} {ΛT : Lat T} (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hv : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f)
    {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓕) {u u' : WO S T}
    (hu : u.map (infPart D) = 0) (hu' : u'.map (infPart D) = 0) (hn : u - u' ∉ latO S T ΛS ΛT fun _ => True) :
    GlobalTheory.Ker.ipO μ 𝓕 (heisO ψ S T u f) (heisO ψ S T u' f) = 0 := by
  obtain ⟨h1, -, h3⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  have h0 : (u - u').map (infPart D) = 0 := by
    funext i j
    have a : infPart D (u i j) = 0 := congrFun (congrFun hu i) j
    have b : infPart D (u' i j) = 0 := congrFun (congrFun hu' i) j
    show infPart D (u i j - u' i j) = 0
    rw [RingHom.map_sub, a, b, sub_self]
  rw [h1 _ h0] at hn
  push_neg at hn
  obtain ⟨l, hl, hne⟩ := hn
  obtain ⟨ε, hε, hεf⟩ := h3 f hv l hl
  have t1 := GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hf hu
  have t2 := GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hf hu'
  have e := GlobalTheory.Size.ipO_heisO hψ hμ.1 hμ.2.1 t1 t2 l
  rw [heisO_comm l u, heisO_comm l u', hεf f hv, heisO_smul, heisO_smul, GlobalTheory.Size.ipO_smul_left, GlobalTheory.Size.ipO_smul_left,
    GlobalTheory.Size.ipO_smul_right, GlobalTheory.Size.ipO_smul_right] at e
  have hεε : ε * starRingEnd ℂ ε = 1 := by rcases hε with rfl | rfl <;> simp
  have n1 := GlobalTheory.HeisOrtho.mul_conj_of_norm_one (hψ.1.2.1 (symplO S T l u'))
  have e2 : ψ (symplO S T (u - u') l) * ψ (symplO S T l u) = ψ (symplO S T l u') := by
    rw [← AddChar.map_add_eq_mul, GlobalTheory.OrientedHeis.symplO_skew u l, GlobalTheory.OrientedHeis.symplO_skew u' l]
    congr 1
    have : symplO S T (u - u' + u') l = symplO S T (u - u') l + symplO S T u' l := by
      unfold symplO hO
      simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add]
    rw [sub_add_cancel] at this
    linear_combination -this
  refine (mul_eq_zero.1 (?_ : (ψ (symplO S T (u - u') l) - 1) * _ = 0)).resolve_left (sub_ne_zero.2 hne)
  set I := GlobalTheory.Ker.ipO μ 𝓕 (heisO ψ S T u f) (heisO ψ S T u' f)
  set A := ψ (symplO S T (u - u') l)
  set B := ψ (symplO S T l u)
  set C := ψ (symplO S T l u')
  linear_combination (-A) * e + (ε * starRingEnd ℂ C * starRingEnd ℂ ε * I) * e2 +
    (C * starRingEnd ℂ C * I) * hεε + I * n1

theorem ip_sum (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓕)
    {ι : Type} (s : Finset ι) (a : ι → ℂ) (h : ι → WO S T → ℂ) (c : ℂ) (ht : ∀ i, IsThetaFunO ψ S T (h i))
    (ha : ∀ i, a i * starRingEnd ℂ (a i) = 1)
    (ho : ∀ i j, i ≠ j → GlobalTheory.Ker.ipO μ 𝓕 (h i) (h j) = 0) (hc : ∀ i, GlobalTheory.Ker.ipO μ 𝓕 (h i) (h i) = c) :
    GlobalTheory.Ker.ipO μ 𝓕 (∑ i ∈ s, a i • h i) (∑ i ∈ s, a i • h i) = s.card * c := by
  have e : ∀ w, (∑ i ∈ s, a i • h i) w * starRingEnd ℂ ((∑ i ∈ s, a i • h i) w) =
      ∑ i ∈ s, ∑ j ∈ s, (a i * starRingEnd ℂ (a j)) * (h i w * starRingEnd ℂ (h j w)) := fun w => by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hi : ∀ i j, Integrable (fun w => (a i * starRingEnd ℂ (a j)) * (h i w * starRingEnd ℂ (h j w))) (μ.restrict 𝓕) :=
    fun i j => Integrable.const_mul (GlobalTheory.Size.integrableOn_mul_conj hψ hμ.1 hμ.2.1 (ht i) (ht j)) _
  have e2 : GlobalTheory.Ker.ipO μ 𝓕 (∑ i ∈ s, a i • h i) (∑ i ∈ s, a i • h i) =
      ∑ i ∈ s, ∑ j ∈ s, (a i * starRingEnd ℂ (a j)) * GlobalTheory.Ker.ipO μ 𝓕 (h i) (h j) := by
    unfold GlobalTheory.Ker.ipO
    simp only [e]
    rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hi i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ fun j _ => hi i j]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  rw [e2, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single_of_mem i hi fun j _ hj => by rw [ho i j hj.symm, mul_zero], ha, hc, one_mul]

theorem selfDual_stdLat (hS : S.gram = 1) : IsSelfDualC S (stdLat S) := by
  convert GlobalTheory.Ker.Base.selfDualC_stdL hS using 1
  ext x
  rw [GlobalTheory.SW.Base.mem_stdL, stdLat, stdL, Submodule.mem_pi]
  refine forall_congr' fun i => ⟨fun h => ?_, fun h _ => ?_⟩
  · obtain ⟨b, hb⟩ := Submodule.mem_one.1 (h trivial)
    rw [← hb]
    exact b.2
  · exact Submodule.mem_one.2 ⟨⟨x i, h⟩, rfl⟩

theorem reads_sum {θ : InfFam D} {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E}
    {ι : Type} (s : Finset ι) {G : ι → VC D a d → ℂ} {f : ι → WO S T → ℂ} (h : ∀ i, Reads ψ θ hS hT cc δ r (G i) (f i)) :
    Reads ψ θ hS hT cc δ r (∑ i ∈ s, G i) (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).zero_mem, fun w _ => by simp⟩
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi]; exact (h i).add ih

theorem finPt_sub {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (r : D.host.E) (z z' : Matrix (Fin d) (Fin a) D.host.E) :
    finPt hS hT r (z - z') = finPt hS hT r z - finPt hS hT r z' := by
  unfold finPt
  rw [← AddMonoidHom.map_sub]
  congr 1
  ext i j
  simp only [Matrix.of_apply, Matrix.sub_apply]
  ring_nf

theorem pt_sub_mem {a d : ℕ} (δ : ℂ) {z z' : Matrix (Fin d) (Fin a) D.host.E} (h : z - z' ∈ YYl D (stdL D a) (stdL D d)) :
    pt D (tor0 D ⊤ δ) δ z - pt D (tor0 D ⊤ δ) δ z' ∈ La0 D (tor0 D ⊤ δ) a d := by
  refine AddSubgroup.subset_closure ⟨δ, AddSubgroup.subset_closure ⟨1, trivial, by simp⟩, _, h, ?_⟩
  funext τ i j
  simp only [pt, embV, tor0, Pi.sub_apply, Pi.smul_apply, Matrix.sub_apply, smul_eq_mul, map_sub]
  ring

set_option maxHeartbeats 1000000 in

theorem ip_cosetVec : ∀ {D : D7} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (X : Data P) (r : D.host.E), IsExact P X r →
  ∀ (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)) (o : ℕ), GoodMod D 𝔪 Sf →
  ∀ LB : Lat X.B, IsSelfDualC X.B LB →
    (∀ z : Matrix (Fin P.d) (Fin P.a) D.host.E, z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D P.a) (Formalism.MainNotions.StandardLatticesGL3.stdL D P.d) ↔
      finPt X.rkA X.rkB r z ∈ latO X.A X.B (stdLat X.A) LB fun _ => True) →
  ∀ f₀ φ, Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r P.e0 f₀ → IsSphOff X.ψ X.A X.B (stdLat X.A) LB ∅ f₀ →
    Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r (cosetVec P 𝔪 o) φ →
  ∀ (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)), IsCovolOne (ratL X.B X.A) ν 𝓕 →
    ip X.A X.B ν 𝓕 φ φ = ((Ideal.absNorm 𝔪 : ℂ) ^ (P.a * P.d))⁻¹ * ip X.A X.B ν 𝓕 f₀ f₀ := by
  intro D δ t0 Q P X r hX 𝔪 Sf o hG LB hLB hY f₀ φ hf₀ hsph hφ ν 𝓕 hcov
  have hset := hX.setup
  have hψ := hset.std
  have hN0 : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 hG.1)
  have hidx := GlobalTheory.SkewIndex.index_inter_skew D δ P.crv 𝔪 hG.1 (Ideal.isCoprime_iff_sup_eq.2 hG.2.1) P.a P.d
  have hpts := fun y hy => GlobalTheory.FunObj.StdDatum.SkewPoints.points D δ P.crv 𝔪 hG.1 (a := P.a) (d := P.d) y hy
  unfold cosetVec at hφ
  generalize La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d) = L at hidx hpts hφ
  have hne : ((La0 D (tor0 D ⊤ δ) P.a P.d).addSubgroupOf L).index ≠ 0 := by rw [hidx]; positivity
  haveI : Finite (L ⧸ (La0 D (tor0 D ⊤ δ) P.a P.d).addSubgroupOf L) := AddSubgroup.index_ne_zero_iff_finite.1 hne
  letI : Fintype (L ⧸ (La0 D (tor0 D ⊤ δ) P.a P.d).addSubgroupOf L) := Fintype.ofFinite _
  choose z hz _ using fun q : L ⧸ (La0 D (tor0 D ⊤ δ) P.a P.d).addSubgroupOf L => hpts _ (Quotient.out q).2
  have hlv : IsLatVac (heisO X.ψ X.A X.B) (latO X.A X.B (stdLat X.A) LB fun _ => True) f₀ := by
    have e : (fun v : FinPl D => v ∉ (∅ : Finset (FinPl D))) = fun _ => True := by funext v; simp
    rw [← e]
    exact hsph
  have hfin : ∀ y, (finPt X.rkA X.rkB r y).map (infPart D) = 0 := fun y => GlobalTheory.VacUnique.finRat_inf _ _ _
  have hrd := GlobalTheory.NormExact.heisO_finPt_reads X.ψ X.θ X.A X.B X.rkA X.rkB ⊤ δ r hset
  set n := ((La0 D (tor0 D ⊤ δ) P.a P.d).addSubgroupOf L).index with hn
  have eI : Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) L P.e0 = ((Real.sqrt (n : ℝ) : ℂ))⁻¹ •
      ∑ q, al D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (z q)) • U D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (z q)) P.e0 := by
    funext y
    simp only [Iop, finsum_eq_sum_of_fintype, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, hz, ← hn]
  have hg := reads_sum Finset.univ fun q => (hrd _ _ hf₀ (z q)).smul (al D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (z q)))
  have hg2 := hg.smul ((Real.sqrt (n : ℝ) : ℂ))⁻¹
  rw [← eI] at hg2
  have hw := ((hrd _ _ hg2 (unitBlock D o P.a P.d)).smul
    (wdPh D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o P.a P.d)))).smul
    ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (P.a * P.d)) : ℂ))⁻¹
  have hsum := ip_sum hψ hcov Finset.univ (fun q => al D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (z q)))
    (fun q => heisO X.ψ X.A X.B (finPt X.rkA X.rkB r (z q)) f₀) (GlobalTheory.Ker.ipO ν 𝓕 f₀ f₀) (fun q => (hrd _ _ hf₀ (z q)).1)
    (fun q => by
      rw [al, map_zpow₀, ← mul_zpow]
      simp)
    (fun q q' hq => ip_heisO_eq_zero hψ (selfDual_stdLat hset.gS) hLB hf₀.1 hlv hcov (hfin _) (hfin _) fun h => hq (by
      rw [← finPt_sub, ← hY] at h
      have h2 := pt_sub_mem δ h
      rw [← hz, ← hz] at h2
      rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', eq_comm, QuotientAddGroup.eq,
        AddSubgroup.mem_addSubgroupOf, neg_add_eq_sub]
      exact h2))
    fun q => GlobalTheory.Size.ipO_heisO hψ hcov.1 hcov.2.1 hf₀.1 hf₀.1 _
  have hph : ∀ x : VC D P.a P.d, wdPh D (tor0 D ⊤ δ) x * starRingEnd ℂ (wdPh D (tor0 D ⊤ δ) x) = 1 := fun x =>
    GlobalTheory.HeisOrtho.mul_conj_of_norm_one (by simp [wdPh, Formalism.MainNotions.StandardLatticesGL3.ee, Complex.norm_exp])
  have hsq : ∀ t : ℝ, 0 ≤ t → ((Real.sqrt t : ℂ))⁻¹ * starRingEnd ℂ ((Real.sqrt t : ℂ))⁻¹ = (t : ℂ)⁻¹ := fun t ht => by
    rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt ht]
  have e1 := hsq n (Nat.cast_nonneg n)
  have e2 := hsq ((Ideal.absNorm 𝔪 : ℝ) ^ (P.a * P.d)) (by positivity)
  have e3 := hph (pt D (tor0 D ⊤ δ) δ (unitBlock D o P.a P.d))
  have e4 : ((n : ℝ) : ℂ)⁻¹ * (n : ℂ) = 1 := by
    rw [Complex.ofReal_natCast]; exact inv_mul_cancel₀ (Nat.cast_ne_zero.2 hne)
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, ← AddSubgroup.index_eq_card, ← hn] at hsum
  have eW : ∀ (x : VC D P.a P.d) G, Wd D (tor0 D ⊤ δ) x G = wdPh D (tor0 D ⊤ δ) x • U D (tor0 D ⊤ δ) x G := fun _ _ => rfl
  rw [eW] at hφ
  rw [Reads.unique hφ hw]
  show GlobalTheory.Ker.ipO ν 𝓕 _ _ = _ * GlobalTheory.Ker.ipO ν 𝓕 f₀ f₀
  rw [GlobalTheory.Size.ipO_smul_left, GlobalTheory.Size.ipO_smul_right, GlobalTheory.Size.ipO_smul_left, GlobalTheory.Size.ipO_smul_right,
    GlobalTheory.Size.ipO_heisO hψ hcov.1 hcov.2.1 hg2.1 hg2.1, GlobalTheory.Size.ipO_smul_left, GlobalTheory.Size.ipO_smul_right, hsum,
    ← mul_assoc, e2, ← mul_assoc (wdPh _ _ _), e3, one_mul, ← mul_assoc _ (starRingEnd ℂ _), e1, ← mul_assoc _ (n : ℂ), e4, one_mul]
  push_cast
  rfl

end GlobalTheory.NormRatio.CosetNorm
