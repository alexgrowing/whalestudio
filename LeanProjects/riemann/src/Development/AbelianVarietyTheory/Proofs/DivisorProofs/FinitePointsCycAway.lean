import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteFibrePoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectPullbackLevelPowerCalculus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomLift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIffEighthPowerPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EighthPowerShapeDependsOnlyOnMatrices
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointDeterminesShapeComplex
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BijectiveTensorOmegaStd

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.SiegLev

noncomputable section

namespace GlobalTheory.ThetaQuasiFinite

theorem exists_spMap {R R' : Type} [CommRing R] [CommRing R'] (x : Sp R' ⟶ Sp R) : ∃ β : R →+* R', spMap β = x :=
  ⟨(Spec.preimage x).hom, Spec.map_preimage x⟩

theorem finite_points_cycAway {n : ℕ} (hn : n ≠ 0) (K : Type) [Field K] : Finite (Sp K ⟶ Sp (cycAway n)) := by
  have h₁ : Finite (cycAway n →+* K) := by
    have hf : Finite {z : K | z ^ n = 1} := by
      refine ((Polynomial.nthRoots n (1 : K)).finite_toSet.subset fun z hz => ?_).to_subtype
      exact (Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hn)).2 hz
    refine Finite.of_injective (fun β : cycAway n →+* K =>
      (⟨β (zetaAway n), (isPrimitiveRoot_map hn β).pow_eq_one⟩ : {z : K | z ^ n = 1})) fun β β' e => ?_
    have e' : β (zetaAway n) = β' (zetaAway n) := congrArg Subtype.val e
    ext ⟨x, hx⟩
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact e'
      · have h0 : (n : cycAway n) * ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ = 1 :=
          Subtype.ext (by simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn : (n : ℂ) ≠ 0))
        have a := congrArg β h0
        have a' := congrArg β' h0
        rw [map_mul, map_natCast, map_one] at a a'
        exact (eq_inv_of_mul_eq_one_right a).trans (eq_inv_of_mul_eq_one_right a').symm
    | zero => exact (map_zero β).trans (map_zero β').symm
    | one => exact (map_one β).trans (map_one β').symm
    | add x y hx hy ihx ihy =>
      exact (map_add β ⟨x, hx⟩ ⟨y, hy⟩).trans ((congrArg₂ (· + ·) ihx ihy).trans (map_add β' ⟨x, hx⟩ ⟨y, hy⟩).symm)
    | neg x hx ih => exact (map_neg β ⟨x, hx⟩).trans ((congrArg (- ·) ih).trans (map_neg β' ⟨x, hx⟩).symm)
    | mul x y hx hy ihx ihy =>
      exact (map_mul β ⟨x, hx⟩ ⟨y, hy⟩).trans ((congrArg₂ (· * ·) ihx ihy).trans (map_mul β' ⟨x, hx⟩ ⟨y, hy⟩).symm)
  exact Finite.of_surjective (fun β : cycAway n →+* K => spMap β) exists_spMap

theorem finite_pow_eq {K : Type} [Field K] {m : ℕ} (hm : 1 ≤ m) (a : K) : Set.Finite {z : K | z ^ m = a} :=
  (Polynomial.nthRoots m a).finite_toSet.subset fun _ hz => (Polynomial.mem_nthRoots hm).2 hz

theorem finite_esymm_eq {K A : Type} [Field K] [Fintype A] {M : ℕ} (hM : 1 ≤ M) (e : Fin (Fintype.card A) → ℕ)
    (he : ∀ i, 1 ≤ e i) (E : Fin (Fintype.card A) → K) :
    Set.Finite {v : A → K | ∀ i : Fin (Fintype.card A),
      ((Finset.univ.val.map (fun a => v a ^ M)).esymm ((i : ℕ) + 1)) ^ e i = E i} := by
  classical
  let σ : (A → K) → Fin (Fintype.card A) → K := fun v i => (Finset.univ.val.map (fun a => v a ^ M)).esymm ((i : ℕ) + 1)
  refine Set.Finite.of_finite_fibers σ
    ((Set.Finite.pi' fun i => finite_pow_eq (he i) (E i)).subset ?_) ?_
  · rintro _ ⟨v, hv, rfl⟩ i
    exact hv i
  · rintro _ ⟨v₀, -, rfl⟩
    refine (Set.Finite.pi' fun _ : A => Set.finite_iUnion fun b : A => finite_pow_eq hM (v₀ b ^ M)).subset ?_
    rintro v ⟨-, hv⟩ a
    have hv' : σ v = σ v₀ := hv
    have hp : ((Finset.univ.val.map (fun a => v a ^ M)).map fun t => Polynomial.X - Polynomial.C t).prod =
        ((Finset.univ.val.map (fun a => v₀ a ^ M)).map fun t => Polynomial.X - Polynomial.C t).prod := by
      rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm]
      simp only [Multiset.card_map, Finset.card_val, Finset.card_univ]
      refine Finset.sum_congr rfl fun j hj => ?_
      rcases j with _ | j
      · simp [Multiset.esymm]
      · have := congrFun hv' ⟨j, by simpa using hj⟩
        simp only [σ] at this
        rw [this]
    have hr := congrArg Polynomial.roots hp
    rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hr
    have hm : v a ^ M ∈ Finset.univ.val.map (fun a => v₀ a ^ M) :=
      hr ▸ Multiset.mem_map_of_mem _ (Finset.mem_univ a)
    obtain ⟨b, -, hb⟩ := Multiset.mem_map.1 hm
    exact Set.mem_iUnion.2 ⟨b, hb.symm⟩

section Level

open GlobalTheory.SiegLevCalc GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull

variable {h n n' n'' : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}

theorem siegPB_of_lev {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n' ζ' s'} {f : S' ⟶ S}
    {φ : c'.A.left ⟶ c.A.left} {χ : c''.A.left ⟶ c.A.left} (m : SRelBy c' c 0 0 f φ) (m' : SRelBy c'' c 0 0 f χ)
    (hlev : ∀ a, (c''.lev a).left ≫ χ = (c'.lev a).left ≫ φ) : SiegPB c'' c' (𝟙 _) := by
  obtain ⟨hφ, ⟨φ₂, hs, hw⟩, -⟩ := m
  obtain ⟨hχ, ⟨χ₂, hs', hw'⟩, -⟩ := m'
  have hp := hφ.1
  let F : c''.A.left ⟶ c'.A.left := hp.lift χ (c''.A.hom ≫ 𝟙 _) (by rw [hχ.1.w, Category.comp_id])
  have hF : F ≫ φ = χ := hp.lift_fst _ _ _
  have hFw : F ≫ c'.A.hom = c''.A.hom ≫ 𝟙 _ := hp.lift_snd _ _ _
  let U : Over.mk ((c''.A ⊗ c''.A).hom ≫ 𝟙 _) ⟶ c'.A ⊗ c'.A :=
    lift (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A))
  let F₂ : (c''.A ⊗ c''.A).left ⟶ (c'.A ⊗ c'.A).left := U.left
  have h₁ : F₂ ≫ (fst c'.A c'.A).left = (fst c''.A c''.A).left ≫ F :=
    congrArg (fun q => q.left) (lift_fst (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A)))
  have h₂ : F₂ ≫ (snd c'.A c'.A).left = (snd c''.A c''.A).left ≫ F :=
    congrArg (fun q => q.left) (lift_snd (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A)))
  have h₃ : F₂ ≫ φ₂ = χ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst c.A c.A).left = _ ≫ (fst c.A c.A).left
      rw [Category.assoc, hs.1, ← Category.assoc, h₁, Category.assoc, hF, hs'.1]
    · show (_ ≫ _) ≫ (snd c.A c.A).left = _ ≫ (snd c.A c.A).left
      rw [Category.assoc, hs.2, ← Category.assoc, h₂, Category.assoc, hF, hs'.2]
  refine ⟨F, F₂, hφ.cancel (by rw [hF, Category.id_comp]; exact hχ) hFw, ⟨h₁, h₂⟩, ?_, fun a => ?_⟩
  · rw [← h₃] at hw'
    exact (hw'.trans c''.isLB (pull_isLB c.isLB _) (pull_isLB (pull_isLB c.isLB _) _)
      (iso_pull_pull c.isLB φ₂ F₂).symm).trans c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c'.isLB _)
      (iso_pull F₂ hw).symm
  · apply hp.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hF).trans ((hlev a).trans
        (congrArg (· ≫ φ) (Category.id_comp _).symm)))
    · have a₁ : (c''.lev a).left ≫ c''.A.hom = 𝟙 S' := Over.w (c''.lev a)
      have a₂ : (c'.lev a).left ≫ c'.A.hom = 𝟙 S' := Over.w (c'.lev a)
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hFw).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ 𝟙 _) a₁).trans ((Category.id_comp _).trans ((Category.comp_id _).symm.trans
          ((congrArg (𝟙 _ ≫ ·) a₂.symm).trans (Category.assoc _ _ _).symm))))))

theorem sRel_zero_of_siegPB {c : SiegPre h n ζ s} {c' : SiegPre h n ζ' s'} {f : S' ⟶ S} (m : SiegPB c' c f) :
    SRel c' c 0 0 f := by
  simpa using sRel_mul ((sRel_one_one_iff c' c f).2 m) 0

theorem finite_of_fibre (hn : 1 ≤ n) (F : SFam h n ζ) (K : Type) [Field K] [IsAlgClosed K] (x₀ : Sp K ⟶ Sp B)
    {t : Sp K ⟶ Sp B'} (c₀ : SiegPre h n' ζ' t) :
    Set.Finite {y : Sp K ⟶ F.X | y ≫ F.s = x₀ ∧ SRel c₀ F.univ 0 0 y} := by
  have hT := AbTorsionFinite.finite_torsion K c₀.A c₀.ab n hn
  have ex : ∀ y : {y : Sp K ⟶ F.X | y ≫ F.s = x₀ ∧ SRel c₀ F.univ 0 0 y},
      ∃ (C : SiegPre h n ζ x₀) (ψ : C.A.left ⟶ c₀.A.left), SiegPB C F.univ y.1 ∧ SRelBy C c₀ 0 0 (𝟙 _) ψ := by
    rintro ⟨y, hy, hr⟩
    obtain ⟨C, hC⟩ := (siegPre_pullback h n B ζ _ _ F.s x₀ y F.univ hy).1
    obtain ⟨ψ, hψ⟩ := sRel_cancel (f' := 𝟙 _) hr (by rw [Category.id_comp]; exact sRel_zero_of_siegPB hC)
    exact ⟨C, ψ, hC, hψ⟩
  choose C ψ hC hψ using ex
  let U : 𝟙_ (Over (Sp K)) ⟶ Over.mk ((𝟙_ (Over (Sp K))).hom ≫ 𝟙 _) := Over.homMk (𝟙 _) (by simp)
  let lam := fun y => ((preHom (G := c₀.A) U).comp (pushHom (hψ y).1 (𝟙_ _)))
  let Λ : _ → (Fin h ⊕ Fin h → ℤ) →+ Additive (𝟙_ (Over (Sp K)) ⟶ c₀.A) := fun y =>
    AddMonoidHom.mk' (fun a => Additive.ofMul (lam y ((C y).lev a))) fun v w => by
      rw [(C y).lev_add, map_mul, ofMul_mul]
  refine Set.finite_coe_iff.1 (Finite.of_injective (fun y (i : Fin h ⊕ Fin h) =>
    (⟨lam y ((C y).lev (Pi.single i 1)), by rw [← map_pow, (C y).lev_tors, map_one]⟩ :
      {x : 𝟙_ (Over (Sp K)) ⟶ c₀.A // x ^ n = 1})) fun y y' e => ?_)
  have E : (Λ y).toIntLinearMap = (Λ y').toIntLinearMap := by
    refine (Pi.basisFun ℤ _).ext fun i => ?_
    rw [Pi.basisFun_apply]
    exact congrArg Additive.ofMul (congrArg Subtype.val (congrFun e i))
  have hl : ∀ a, ((C y).lev a).left ≫ ψ y = ((C y').lev a).left ≫ ψ y' := fun a => by
    have := congrArg (fun z => (Additive.toMul z).left) (LinearMap.congr_fun E a)
    exact (Category.id_comp _).symm.trans (this.trans (Category.id_comp _))
  have m := siegPB_of_lev (hψ y') (hψ y) hl
  have m' : SiegPB (C y) F.univ y'.1 := by
    have := sRel_comp ((sRel_one_one_iff _ _ _).2 (hC y')) ((sRel_one_one_iff _ _ _).2 m)
    rwa [Category.id_comp, sRel_one_one_iff] at this
  exact Subtype.ext (F.inj K y.1 y'.1 x₀ (C y) (y.2.1.trans y'.2.1.symm) (hC y) m')

end Level

section Sharp

open GlobalTheory.SharpShape GlobalTheory.CechPic

variable {h g : ℕ}

theorem exists_shape (hL : Out.Laws) {W : Matrix (Fin 8) (Fin 8) ℤ} (hW : IsE8 W) {J : Type} [Finite J]
    (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) :
    ∃ (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ), ∀ (k : ℕ), k ≠ 0 → ∀ (o : Type) [CommRing o] (b : TBase o k)
      (S : Scheme.{0}) (s : S ⟶ Sp o) (c : SiegPre h k (b.ζ : o) s) (t : TObj g k J b s), c.Principal →
      IsSharp W a bas t c → t.Shape Mat κ := by
  classical
  have hκ : ∀ j, ∃ κ₀ : ℕ, ∀ κ : ℕ, κ₀ ≤ κ →
      ((((κ : ℤ) • W - (a j).transpose * W * a j) + ((κ : ℤ) • W - (a j).transpose * W * a j).transpose).map
        (Int.cast : ℤ → ℝ)).PosDef := fun j => by
    have hB : (((a j).transpose * (W + W.transpose) * a j).map (Int.cast : ℤ → ℝ)).IsHermitian := by
      have : ((a j).transpose * (W + W.transpose) * a j).transpose = (a j).transpose * (W + W.transpose) * a j := by
        simp only [Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_transpose, Matrix.mul_assoc, add_comm]
      ext u v
      simpa using congrArg (Int.cast : ℤ → ℝ) (congrFun (congrFun this u) v)
    obtain ⟨κ₀, hκ₀⟩ := TensorSiegel.exists_posDef_smul_sub hW.1 hB
    refine ⟨κ₀, fun κ hκ => ?_⟩
    convert hκ₀ κ hκ using 1
    have : ((κ : ℤ) • W - (a j).transpose * W * a j) + ((κ : ℤ) • W - (a j).transpose * W * a j).transpose =
        (κ : ℤ) • (W + W.transpose) - (a j).transpose * (W + W.transpose) * a j := by
      simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_transpose,
        Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, smul_add]
      abel
    rw [this]
    ext u v
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_sub, Int.cast_mul,
      Int.cast_natCast]
  choose κ₀ hκ₀ using hκ
  obtain ⟨κ, hκ⟩ : ∃ κ : ℕ, ∀ j, κ₀ j ≤ κ := (Set.finite_range κ₀).bddAbove.imp fun κ hκ j => hκ ⟨j, rfl⟩
  refine ⟨fun j => Matrix.of fun i' i => bas.symm (fun u => ∑ v, a j u v • bas (Pi.single i 1) v) i', κ, ?_⟩
  rintro k hk o _ b S s c t hc ⟨pr, hpr, hprod, hiso, hact, hpt⟩ j
  haveI : NeZero k := ⟨hk⟩
  refine ⟨fun i => ?_, ?_⟩
  · refine (label_iff c t pr hpr hprod (a j) _ (hact j) (fun i => bas (Pi.single i 1)) hpt i _).2 fun u => ?_
    set z := bas.symm (fun u => ∑ v, a j u v • bas (Pi.single i 1) v) with hz
    have hx : z = ∑ p, z p • (Pi.single p 1 : Fin (2 * g) → ℤ) := by
      ext q; simp [Finset.sum_apply, Pi.single_apply]
    have h1 : (fun u => ∑ v, a j u v • bas (Pi.single i 1) v) = ∑ p, z p • bas (Pi.single p 1) := by
      have : bas z = (fun u => ∑ v, a j u v • bas (Pi.single i 1) v) := by
        rw [hz, LinearEquiv.apply_symm_apply]
      rw [← this]
      conv_lhs => rw [hx]
      simp only [map_sum, map_zsmul]
    have h2 : ∑ v, a j u v • bas (Pi.single i 1) v = ∑ p, z p • bas (Pi.single p 1) u := by
      simpa [Finset.sum_apply] using congrFun h1 u
    have h3 : ∑ v, a j u v • bas (Pi.single i 1) v - ∑ i', ((((z i' : ℤ) : ZMod k).val : ℕ) : ℤ) • bas (Pi.single i' 1) u =
        k • ∑ p, (z p / k) • bas (Pi.single p 1) u := by
      rw [h2, ← Finset.sum_sub_distrib, Finset.smul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← sub_smul, ZMod.val_intCast, ← natCast_zsmul, smul_smul, Int.emod_def, sub_sub_cancel]
    exact (congrArg (fun x => levHom c (Out.baseOver S) (Multiplicative.ofAdd x)) h3).trans (levHom_nsmul c _ _)
  · set W' := (κ : ℤ) • W - (a j).transpose * W * a j with hW'
    have amp := GlobalTheory.T.relAmple_formBundle_power_of_posDef hL.globalFns h k 8 o _ S s c t.A pr W' hpr hprod hc.1 (hκ₀ j κ (hκ j))
    have e := cls_shape hL.globalFns c hc.1 t pr W (a j) hiso _ (hact j) κ
    have hB := LB.isLB_linComb c.isLB (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left)
      (fun uv => W' uv.1 uv.2)
    rw [← cls_linComb c.isLB _ _ hB] at e
    have := t.ab.proper
    have hM := LB.isLB_linComb t.isLB (K := Fin 2) ![𝟙 t.A.left, (t.act j).left] ![(κ : ℤ), -1]
    refine relAmple_of_isAmpleLB t.A hM fun U hU =>
      (isAmpleLB_of_relAmple t.A hB amp U hU).of_lbIso (pull_isLB hM _) ?_
    rw [← cls_eq_iff (pull_isLB hM _) (pull_isLB hB _), cls_pull hM, cls_pull hB, e]

theorem tMap_of_hasTh (hL : Out.Laws) (hL2 : Out.Laws2) (J : Type) [Finite J]
    (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (hn : n.Prime) (hodd : Odd n) :
    ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (K : Type) [Field K] [IsAlgClosed K]
      (s : Sp K ⟶ Sp o) (t t' : TObj g ((n ^ j) ^ 2) J b s) (v : Ix g ((n ^ j) ^ 2) → K),
      t.Shape Mat κ → t'.Shape Mat κ → t.HasTh (𝟙 _) v → t'.HasTh (𝟙 _) v → TMap t' t (𝟙 _) := by
  obtain ⟨j₀, H⟩ := GlobalTheory.T.exists_theta_family_from_very_dense_points hL hL2 g J Mat κ n hn hodd
  refine ⟨j₀, fun j hj o _ b K _ _ s t t' v h1 h1' h2 h2' => ?_⟩
  have hid : spMap (RingHom.id K) = 𝟙 (Sp K) := Spec.map_id (CommRingCat.of K)
  obtain ⟨em, hem⟩ := exists_spMap s
  obtain rfl : s = spMap (RingHom.id K) ≫ spMap em := by rw [hid, Category.id_comp, hem]
  have hvd : VeryDense (objPrimes b Mat κ em v) := by
    intro q f hq hf
    have hq0 : q = ⊥ := (Ideal.eq_bot_or_top q).resolve_right hq.ne_top
    subst hq0
    refine ⟨⊥, ⟨K, inferInstance, inferInstance, RingHom.id K, t, ?_, h1, h2⟩, hq, le_rfl, hf⟩
    exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.id K).injective
  obtain ⟨t₀, -, h₀⟩ := H j hj o b K em v hvd
  have m := h₀ K (RingHom.id K) t h1 h2
  have m' := h₀ K (RingHom.id K) t' h1' h2'
  refine ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g _ J b _ _ _ _ _ _ t₀ t t').2 _ (𝟙 _) m).2 ?_
  rwa [Category.id_comp]

theorem exists_act {W : Matrix (Fin 8) (Fin 8) ℤ} {J : Type} {a : J → Matrix (Fin 8) (Fin 8) ℤ}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))} {N' : ℕ} {o : Type} [CommRing o]
    {b : TBase o (N' ^ 2)} {S : Scheme.{0}} {s : S ⟶ Sp o} {c : SiegPre h (N' ^ 2) (b.ζ : o) s}
    {t : TObj g (N' ^ 2) J b s} (H : IsSharp W a bas t c) :
    ∃ t' : TObj g (N' ^ 2) (Fin 8 × Fin 8) b s, IsSharp W (fun uv => Matrix.single uv.1 uv.2 1) bas t' c ∧
      ∀ (K : Type) [Field K] (x : Sp K ⟶ S) (v : Ix g (N' ^ 2) → K), t.HasTh x v → t'.HasTh x v := by
  obtain ⟨pr, hpr, hprod, hiso, -, hpt⟩ := H
  choose e he _ using fun uv : Fin 8 × Fin 8 =>
    hprod t.A fun w => (List.ofFn fun v => pr v ^ (Matrix.single uv.1 uv.2 (1 : ℤ)) w v).prod
  have hm : ∀ (uv : Fin 8 × Fin 8) w, IsMonHom (e uv ≫ pr w) := fun uv w => by
    rw [he, List.prod_ofFn]
    exact Finset.prod_induction _ (fun x => IsMonHom x) (fun x y _ _ => GlobalTheory.Serre.isMonHom_mul x y)
      GlobalTheory.Serre.isMonHom_one fun i _ => haveI := hpr i; GlobalTheory.Serre.isMonHom_zpow _ _
  have hhom : ∀ uv, IsMonHom (e uv) := fun uv => by
    refine ⟨(hprod _ fun w => η[t.A] ≫ pr w).unique (fun w => ?_) fun _ => rfl,
      (hprod _ fun w => μ[t.A] ≫ e uv ≫ pr w).unique (fun w => Category.assoc _ _ _) fun w => ?_⟩
    · have := hm uv w
      have := hpr w
      rw [Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
    · have := hm uv w
      have := hpr w
      rw [Category.assoc, IsMonHom.mul_hom, IsMonHom.mul_hom, ← Category.assoc, tensorHom_comp_tensorHom]
  exact ⟨{ t with act := e, hom := hhom }, ⟨pr, hpr, hprod, hiso, he, hpt⟩, fun _ _ _ _ hv => hv⟩

end Sharp

open GlobalTheory.SiegLevCalc in

theorem finite_of_hasTh (h g ℓ : ℕ) (hℓ : ℓ.Prime) (ho : Odd ℓ) {W : Matrix (Fin 8) (Fin 8) ℤ}
    (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (hW : IsE8 W) :
    ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (n : ℕ), 1 ≤ n → ∀ (o o' : Type) [CommRing o] [CommRing o'] (ζ : o) (F : SFam h n ζ)
      (b : TBase o' ((ℓ ^ j) ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o') (q : S ⟶ F.X)
      (c : SiegPre h ((ℓ ^ j) ^ 2) (b.ζ : o') s) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ)
      (t : TObj g ((ℓ ^ j) ^ 2) J b s), SRel c F.univ 0 0 q → IsSharp W a bas t c →
      ∀ (K : Type) [Field K] [IsAlgClosed K] (x₀ : Sp K ⟶ Sp o) (s₀ : Sp K ⟶ Sp o') (v : Ix g ((ℓ ^ j) ^ 2) → K),
        Set.Finite {y : Sp K ⟶ F.X | y ≫ F.s = x₀ ∧ ∃ y' : Sp K ⟶ S, y' ≫ s = s₀ ∧ y' ≫ q = y ∧ t.HasTh y' v} := by
  obtain ⟨hL, hL2⟩ := abelianSchemeLaws_all
  obtain ⟨Mat, κ, hsh⟩ := exists_shape hL hW (fun uv : Fin 8 × Fin 8 => Matrix.single uv.1 uv.2 (1 : ℤ)) bas
  obtain ⟨j₀, hj₀⟩ := tMap_of_hasTh hL hL2 (Fin 8 × Fin 8) Mat κ ℓ hℓ ho
  refine ⟨j₀, fun j hj n hn o o' _ _ ζ F b S s q c J a t₁ hq H₁ K _ _ x₀ s₀ v => ?_⟩
  have hk : (ℓ ^ j) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  have hc : c.Principal := sRel_principal hq F.princ
  obtain ⟨t, H, hth⟩ := exists_act H₁
  have he : ∀ u v : Fin 8, ∃ j : Fin 8 × Fin 8, Matrix.single j.1 j.2 (1 : ℤ) = Matrix.single u v 1 :=
    fun u v => ⟨(u, v), rfl⟩
  have fib : ∀ y' : Sp K ⟶ S, y' ≫ s = s₀ → t₁.HasTh y' v →
      ∃ (c' : SiegPre h ((ℓ ^ j) ^ 2) (b.ζ : o') s₀) (t' : TObj g ((ℓ ^ j) ^ 2) (Fin 8 × Fin 8) b s₀), c'.Principal ∧
        IsSharp W (fun uv => Matrix.single uv.1 uv.2 1) bas t' c' ∧ t'.HasTh (𝟙 _) v ∧
        SRel c' F.univ 0 0 (y' ≫ q) := fun y' hy hv => by
    obtain ⟨t', ht'⟩ := tObj_pull o' g _ _ b _ _ s s₀ y' t hy
    obtain ⟨c', hc', H'⟩ := SharpPull.sharp_pull h g _ W _ _ bas o' b _ _ s s₀ y' t t' c hy ht' hc H
    refine ⟨c', t', hc', H', (hasTh_iff_of_tmap o' g _ _ b _ _ t _ _ t' y' K _ v ht').2 ?_,
      sRel_comp hq (sRel_zero_of_siegPB (PowerPullback.backward hL.globalFns hW hc hc' H H' he ht'))⟩
    rw [Category.id_comp]
    exact hth K y' v hv
  rcases Set.eq_empty_or_nonempty
    {y : Sp K ⟶ F.X | y ≫ F.s = x₀ ∧ ∃ y' : Sp K ⟶ S, y' ≫ s = s₀ ∧ y' ≫ q = y ∧ t₁.HasTh y' v} with h0 | h0
  · rw [h0]
    exact Set.finite_empty
  obtain ⟨_, -, y₀, hy₀, -, hv₀⟩ := h0
  obtain ⟨c₀, t₀, hc₀, H₀, hth₀, -⟩ := fib y₀ hy₀ hv₀
  refine (finite_of_fibre hn F K x₀ c₀).subset ?_
  rintro _ ⟨hx, y', hy', rfl, hv'⟩
  obtain ⟨c', t', hc', H', hth', hr⟩ := fib y' hy' hv'
  have m := hj₀ j hj o' b K s₀ t' t₀ v (hsh _ hk o' b _ _ c' t' hc' H') (hsh _ hk o' b _ _ c₀ t₀ hc₀ H₀) hth' hth₀
  have := sRel_comp hr (sRel_zero_of_siegPB (PowerPullback.backward hL.globalFns hW hc' hc₀ H' H₀ he m))
  exact ⟨hx, by rwa [Category.id_comp] at this⟩

theorem finite_theta_fibres : ∀ (h ℓ : ℕ), ℓ.Prime → Odd ℓ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * (8 * h)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (n n' : ℕ), n ≠ 0 → n' ≠ 0 → ∀ (F : SFam h n (zetaAway n)) (b : TBase (cycAway n') ((ℓ ^ j) ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n')) (q : S ⟶ F.X) (c : SiegPre h ((ℓ ^ j) ^ 2) (b.ζ : cycAway n') s) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (t : TObj (8 * h) ((ℓ ^ j) ^ 2) J b s), SRel c F.univ 0 0 q → IsSharp W a bas t c → ∀ (K : Type) [Field K] [IsAlgClosed K], (∀ v : Ix (8 * h) ((ℓ ^ j) ^ 2) → K, Set.Finite {y : Sp K ⟶ F.X | ∃ y' : Sp K ⟶ S, y' ≫ q = y ∧ t.HasTh y' v}) ∧ ∀ [Fintype (Ix (8 * h) ((ℓ ^ j) ^ 2))] (M N : ℕ), 1 ≤ M → 1 ≤ N → (∀ i : Fin (Fintype.card (Ix (8 * h) ((ℓ ^ j) ^ 2))), ((i : ℕ) + 1) * M ∣ N) → ∀ E : Fin (Fintype.card (Ix (8 * h) ((ℓ ^ j) ^ 2))) → K, Set.Finite {y : Sp K ⟶ F.X | ∃ (y' : Sp K ⟶ S) (v : Ix (8 * h) ((ℓ ^ j) ^ 2) → K) (u : K), u ≠ 0 ∧ y' ≫ q = y ∧ t.HasTh y' v ∧ ∀ i, E i = u * ((Finset.univ.val.map (fun x => v x ^ M)).esymm ((i : ℕ) + 1)) ^ (N / (((i : ℕ) + 1) * M))} := by
  intro h ℓ hℓ ho W bas hW
  obtain ⟨j₀, H⟩ := finite_of_hasTh h (8 * h) ℓ hℓ ho bas hW
  refine ⟨j₀, fun j hj n n' hn hn' F b S s q c J a t hq ht K _ _ => ?_⟩
  have first : ∀ v : Ix (8 * h) ((ℓ ^ j) ^ 2) → K,
      Set.Finite {y : Sp K ⟶ F.X | ∃ y' : Sp K ⟶ S, y' ≫ q = y ∧ t.HasTh y' v} := fun v => by
    have := finite_points_cycAway hn K
    have := finite_points_cycAway hn' K
    refine (Set.finite_iUnion fun x₀ => Set.finite_iUnion fun s₀ =>
      H j hj n (Nat.pos_of_ne_zero hn) _ _ _ F b S s q c J a t hq ht K x₀ s₀ v).subset ?_
    rintro y ⟨y', e, hv⟩
    exact Set.mem_iUnion.2 ⟨_, Set.mem_iUnion.2 ⟨_, rfl, y', rfl, e, hv⟩⟩
  refine ⟨first, fun M N hM hN hd E => ?_⟩
  refine ((finite_esymm_eq hM (fun i => N / (((i : ℕ) + 1) * M))
    (fun i => Nat.div_pos (Nat.le_of_dvd hN (hd i)) (Nat.mul_pos (Nat.succ_pos _) hM)) E).biUnion
      fun v _ => first v).subset ?_
  rintro y ⟨y', v, u, hu, e, hv, hE⟩
  obtain ⟨r, rfl⟩ := IsAlgClosed.exists_pow_nat_eq u hN
  have hr : r ≠ 0 := fun h0 => hu (by rw [h0, zero_pow (by omega)])
  refine Set.mem_biUnion (x := r • v) (fun i => ?_) ⟨y', e, hv.unit_smul hr.isUnit⟩
  have e₁ : Finset.univ.val.map (fun x => (r • v) x ^ M) =
      (Finset.univ.val.map (fun x => v x ^ M)).map (fun z => r ^ M • z) := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun x _ => mul_pow _ _ _
  show (Finset.univ.val.map (fun x => (r • v) x ^ M)).esymm ((i : ℕ) + 1) ^ (N / (((i : ℕ) + 1) * M)) = E i
  rw [e₁, ← Multiset.pow_smul_esymm, hE, smul_eq_mul, mul_pow, ← pow_mul, ← pow_mul, ← Nat.mul_assoc, Nat.mul_comm M,
    Nat.mul_div_cancel' (hd i)]

end GlobalTheory.ThetaQuasiFinite
