import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightLawGoodOfFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawNormClassSumFock
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk

noncomputable section

namespace GlobalTheory.Mem.Col2.MetricTie

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.DivisionValues Matrix
open scoped ComplexOrder

theorem majAt_classSum {K : Type} [Field K] [NumberField K] [StarRing K] (C : CSD K) (hb : C.HasRatBasis) (v : InfinitePlace K)
    (hH : (C.H.map v.embedding).PosDef) {W : Type} [AddCommGroup W] [Module ℂ W] (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (ψ : C.V →ₛₗ[v.embedding] W)
    (hs : ∀ x y, (∀ i, C.bV.repr x i ∈ cmMax K) → v.embedding (C.pair x y) = B (ψ x) (ψ y)) (x : C.Forms) :
    Formalism.HermitianLatticesTheory.majAt C.basis (stdFrame C.H) v x x = ∑ c, ((C.wt c : ℂ))⁻¹ * B (ψ (x.1 c)) (ψ (x.1 c)) := by
  have h1 : Formalism.HermitianLatticesTheory.majAt C.basis (stdFrame C.H) v x x =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin C.dim)) (stdFrame C.H) v (C.basis.equivFun x) (C.basis.equivFun x) := by
    have h2 : ∀ z : C.Forms, Formalism.HermitianLatticesTheory.vecAt C.basis v z =
        Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin C.dim)) v (C.basis.equivFun z) := by
      intro z; funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
    simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, h2]
  have hm : metOf (stdFrame C.H v) = C.H.map v.embedding := (frameOfSpec _ _ hH).2
  have hI : x.1 = ∑ i, C.basis.equivFun x i • (C.basis i : C.Cl → C.V) := by
    rw [← C.I_eq_sum]; simp [CSD.I_apply]
  have hc : ∀ i j, v.embedding (C.H i j) =
      ∑ c, ((C.wt c : ℂ))⁻¹ * B (ψ ((C.basis i : C.Cl → C.V) c)) (ψ ((C.basis j : C.Cl → C.V) c)) := by
    intro i j
    simp only [CSD.H, Matrix.of_apply, CSD.csum, map_sum, map_mul, map_inv₀, map_natCast]
    exact Finset.sum_congr rfl fun c _ => congrArg _ (hs _ _ (C.basis_rat hb i c))
  rw [h1, Formalism.L2.DIV.majAt_eq, hm, hI]
  generalize C.basis.equivFun x = a
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, hc, map_sum, LinearMap.sum_apply, Finset.sum_apply, Pi.smul_apply,
    LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum, Finset.sum_mul, Pi.star_apply,
    starRingEnd_apply, RingHom.id_apply]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => ?_
  ring

section Pol

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem fockF_conj {τ : Type} (f g : MvPolynomial τ ℂ) :
    Formalism.REAL.fockF (MvPolynomial.map (starRingEnd ℂ) f) (MvPolynomial.map (starRingEnd ℂ) g) =
      starRingEnd ℂ (Formalism.REAL.fockF f g) := by
  rw [fockF_eq_sum _ _ f.support (MvPolynomial.support_map_subset _ _), Formalism.REAL.fockF, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map, map_mul, map_mul, map_natCast]
  rfl

theorem nfAll_conj (lam : ι → DomWeight n) (p q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    nfAll lam (MvPolynomial.map (starRingEnd ℂ) p) (MvPolynomial.map (starRingEnd ℂ) q) = starRingEnd ℂ (nfAll lam p q) := by
  rw [nfAll, nfAll, map_div₀, fockF_conj, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← fockF_conj, Formalism.L2.Col.map_extremal]

theorem nfAll_shift (lam lam' : ι → DomWeight n) (c : ℤ) (h : ∀ τ i, (lam' τ).w i = (lam τ).w i + c) :
    nfAll lam' = nfAll lam := by
  have e : ∀ τ, (lam' τ).natW = (lam τ).natW := fun τ => by
    funext i
    have hn : 0 < n := i.pos
    simp only [DomWeight.natW, DomWeight.detShift, dif_pos hn, h]
    congr 1
    ring
  funext p q
  simp only [nfAll, extremal, e]

theorem fnOf_congr {G G' : ι → Matrix (Fin n) (Fin n) ℂ} (sh : ι → ℤ) (M : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (y : Frames G) (y' : Frames G') (h : y'.1 = y.1) :
    fnOf G' sh M P y' = fnOf G sh M P y := by
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, h]

theorem unitary_of_isON {G : ι → Matrix (Fin n) (Fin n) ℂ} (hG : ∀ τ, G τ = 1) (o : Frames G) (ho : o.IsON) (τ : ι) :
    (o.1 τ)ᴴ * o.1 τ = 1 := by
  have h := frame_pos o ho τ (by rw [hG]; exact PosSemidef.one)
  rwa [hG, Matrix.mul_one] at h

end Pol

section Step

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)

omit [NumberField E] [StarRing E] [NumberField K] in

theorem map_pairVr_rat (s : K →+* ℂ) (F F' : VV K lam) (hF : ∀ i, (bVV K lam).repr F i ∈ cmMax K) :
    s (pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) F F') = nfL lam (MvPolynomial.map s F.1) (MvPolynomial.map s F'.1) := by
  have hc : ∀ m, F.1.coeff m ∈ cmMax K := fun m => by
    have h := congrArg Subtype.val ((bVV K lam).sum_repr F)
    simp only [Submodule.coe_sum, Submodule.coe_smul, bVV_coe] at h
    rw [← h, MvPolynomial.coeff_sum]
    refine Subfield.sum_mem _ fun i _ => ?_
    obtain ⟨P, hP⟩ := bVVfun_int K lam i
    rw [MvPolynomial.coeff_smul, hP, MvPolynomial.coeff_map, smul_eq_mul]
    exact mul_mem (hF i) (intCast_mem _ _)
  have h := pairVr_nfAll emb (1 : Matrix (Fin n) (Fin n) E) lam s (stdFrC (embAt s emb))
    (fun τ => by simp [stdFrC, gramC]) F F' (fun m => hc m s)
  have e : Formalism.GradedWeylDivisibility.blockAct ℂ (n := n) (stdFrC (n := n) (embAt s emb)).1 = AlgHom.id ℂ _ := blockAct_one
  rw [h, e, nfL_apply]
  simp [stdFrC]

theorem majAt_step (S : GStep E K n) (hF : FOk emb σ) (hS : S.Ok) (h : (S.fam emb lam).Ok) [inst : Fintype S.Cl] (s : K →+* ℂ)
    (x : (S.hlat emb lam h).V) :
    (Formalism.HermitianLatticesTheory.majAt (S.hlat emb lam h).b (S.hlat emb lam h).X (InfinitePlace.mk s) x x).re =
      ∑ c : S.Cl, (((Nat.card (S.Stab c) : ℕ) : ℂ)⁻¹).re *
        (nfAll lam (MvPolynomial.map s (x.1 c).1) (MvPolynomial.map s (x.1 c).1)).re := by
  have h1 := majAt_classSum (S.csd emb lam h) (LatGood.hasRatBasis S emb σ lam hF hS h) (InfinitePlace.mk s)
    (LatGood.step_gram_posDef S emb σ lam hF hS h _) (nfL lam) ((mapS _).domRestrict (VV K lam))
    (fun F F' hr => map_pairVr_rat emb lam _ F F' hr) x
  refine (congrArg Complex.re h1).trans ?_
  have hi : inst = (S.csd emb lam h).finCl := Subsingleton.elim _ _
  subst hi
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h2 : (S.csd emb lam h).wt c = Nat.card (S.Stab c) := (@Nat.card_eq_fintype_card _ (_)).symm
  rw [h2, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.ofReal_re]
  congr 1
  show (nfAll lam (MvPolynomial.map (InfinitePlace.mk s).embedding (x.1 c).1)
    (MvPolynomial.map (InfinitePlace.mk s).embedding (x.1 c).1)).re = _
  rcases InfinitePlace.embedding_mk_eq s with e | e
  · rw [e]
  · have e' : ComplexEmbedding.conjugate s = (starRingEnd ℂ).comp s := RingHom.ext fun _ => rfl
    rw [e, e', ← MvPolynomial.map_map, nfAll_conj, Complex.conj_re]

theorem norm_step (S : GStep E K n) (hF : FOk emb σ) (hS : S.Ok) (h : (S.fam emb lam).Ok) [Fintype S.Cl]
    {lam' : ι → DomWeight n} (hl : nfAll lam = nfAll lam') {sh : ι → ℤ} (hsh : sh = shiftOf lam)
    {G G' : ι → Matrix (Fin n) (Fin n) ℂ} (hG' : ∀ τ, G' τ = 1) (eY : Fr emb σ n → Frames G) (hY : ∀ y, (eY y).1 = y.1)
    (s : K →+* ℂ) (x : (S.hlat emb lam h).V) (Pc : S.Cl → MvPolynomial (ι × Fin n × Fin n) K)
    (hP : ∀ c z, S.embF emb σ lam h x c z = fnOf G sh 1 (MvPolynomial.map σ (Pc c)) (eY z))
    (o : Frames G') (ho : o.IsON) :
    (Formalism.HermitianLatticesTheory.majAt (S.hlat emb lam h).b (S.hlat emb lam h).X (InfinitePlace.mk s) x x).re =
      ∑ c : S.Cl, (((Nat.card (S.Stab c) : ℕ) : ℂ)⁻¹).re * (∏ τ, ‖(o.1 τ).det‖ ^ (2 * sh τ)) *
        (nfAll lam' (subP o.1 (MvPolynomial.map s (Pc c))) (subP o.1 (MvPolynomial.map s (Pc c)))).re := by
  subst hsh
  rw [majAt_step emb σ lam S hF hS h s x]
  refine Finset.sum_congr rfl fun c _ => ?_
  have e : (x.1 c).1 = Pc c := by
    refine evFr_injective (Gr emb σ n) (shiftOf lam) σ (fr0 emb σ n) (funext fun z => ?_)
    exact (hP c z).trans (fnOf_congr _ _ _ z (eY z) (hY z))
  have hd : ∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf lam τ) = 1 := Finset.prod_eq_one fun τ _ => by
    have h1 : ‖(o.1 τ).det‖ = 1 := norm_deFr o ho τ (by rw [hG']; simp)
    rw [h1, _root_.one_zpow]
  have hu := nfAll_blockAct lam' o.1 (fun τ => mul_eq_one_comm.mp (unitary_of_isON hG' o ho τ))
    (MvPolynomial.map s (Pc c)) (MvPolynomial.map s (Pc c))
  rw [hd, mul_one, e, hl, ← hu]
  rfl

omit [NumberField E] [StarRing E] [NumberField K] [StarRing K] in

theorem ipVal_step {lam' : ι → DomWeight n} (hl : nfAll lam = nfAll lam') {sh : ι → ℤ} (hsh : sh = shiftOf lam)
    {G : ι → Matrix (Fin n) (Fin n) ℂ} (hG : ∀ τ, G τ = 1) (eY : Fr emb σ n → Frames G) (hY : ∀ y, (eY y).1 = y.1)
    (o : Frames G) (ho : o.IsON) (P Q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    ipVal emb σ lam (fun z => fnOf G sh (fun τ => (o.1 τ)⁻¹) P (eY z)) (fun z => fnOf G sh (fun τ => (o.1 τ)⁻¹) Q (eY z)) =
      nfAll lam' Q P := by
  subst hsh
  have hG0 : ∀ τ, Gr emb σ n τ = 1 := fun τ => by simp [gramC]
  simp only [fun P z => fnOf_congr (shiftOf lam) (fun τ => (o.1 τ)⁻¹) P z (eY z) (hY z)]
  rw [← hl]
  exact ipFr_fnOf (Gr emb σ n) lam (fr0 emb σ n) ⟨o.1, o.2⟩ (fun τ => by simp [fr0, stdFrC, gramC])
    (fun τ => by rw [hG0, Matrix.mul_one]; exact unitary_of_isON hG o ho τ) P Q

end Step

theorem shiftOf_lamT {R : Ranks} {ι : Type} [Fintype ι] (hc : ι → HCParam R) (j : ℕ) :
    shiftOf (fun τ => Formalism.L2.Forms.shW (Examples₂.lamOf (hc τ) j) ((j * (R.t + 1) / 2 : ℕ) : ℤ)) =
      shiftOf (GlobalTheory.Mem.Col2.lamT hc j) := by
  refine congrArg shiftOf (funext fun τ => ?_)
  obtain ⟨a, ha⟩ := R.t_odd
  have e1 : j * (R.t + 1) / 2 = j * (a + 1) := by
    rw [ha, show j * (2 * a + 1 + 1) = 2 * (j * (a + 1)) by ring]; omega
  have e2 : (R.t + 1) / 2 = a + 1 := by omega
  simp only [Formalism.L2.Forms.shW, GlobalTheory.Mem.Col2.lamT, GlobalTheory.Mem.Col2.shW, e1, e2]
  congr 1

theorem nfAll_lamT {R : Ranks} {ι : Type} [Fintype ι] (hc : ι → HCParam R) (j : ℕ) :
    nfAll (GlobalTheory.Mem.Col2.lamT hc j) = nfAll fun τ => Examples₂.lamOf (hc τ) j :=
  nfAll_shift _ _ _ fun _ _ => rfl

end GlobalTheory.Mem.Col2.MetricTie

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Mem.Col2.MetricTie.ipV_norm_tie : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi), I.IdY l Z u a i hi eY → IpVTieG (D := (I.rec7 l Z)) (I.fm l u a) eY ∧ NormTieG (D := (I.rec7 l Z)) (I.fm l u a) eY := by
  intro B X I hI hp l Z u a i hi eY hY
  have hg : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hp l Z).2.2.2 i hi).1
  have hG : ∀ (e : (I.rec7 l Z).what₂.Tau → (I.rec7 l Z).host.E →+* ℂ) τ, gramC (gramN (I.rec7 l Z) i hi) e τ = 1 := fun e τ => by
    rw [hg, gramC_one]
  refine ⟨fun c o ho P _ Q _ => ?_, fun s x Pc hP o ho => ?_⟩
  · exact MetricTie.ipVal_step B.fields.emb B.embLL (GlobalTheory.Mem.Col2.lamT (B.hcW u) i) (MetricTie.nfAll_lamT _ _)
      (MetricTie.shiftOf_lamT (B.hcW u) i) (hG _) eY hY o ho P Q
  · exact @MetricTie.norm_step _ _ _ _ _ _ _ _ _ _ _ B.fields.emb B.embLL (GlobalTheory.Mem.Col2.lamT (B.hcW u) i) (I.stp u a i) (base_fOk B)
      ((l.ch u a).step i) ((l.fmL u a).fam i) ((I.chIn u a).clFin (l.ch u a) i) _ (MetricTie.nfAll_lamT _ _) _
      (MetricTie.shiftOf_lamT (B.hcW u) i) _ _ (hG _) eY hY s x Pc hP o ho

end
