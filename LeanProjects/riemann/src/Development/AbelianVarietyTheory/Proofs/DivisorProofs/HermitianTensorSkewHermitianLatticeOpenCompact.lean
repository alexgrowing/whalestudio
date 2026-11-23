import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsMoreTer

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.LatOpenCpt

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem exists_zsmul_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : L.IsLattice E) (z : Fin n → E) : ∃ m : ℤ, m ≠ 0 ∧ m • z ∈ L := by
  first
  | exact @_root_.GlobalTheory.IntegerMultipleMembership.exists_int_smul_mem
  | exact _root_.GlobalTheory.IntegerMultipleMembership.exists_int_smul_mem
  | (apply _root_.GlobalTheory.IntegerMultipleMembership.exists_int_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegerMultipleMembership.exists_int_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegerMultipleMembership.exists_int_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegerMultipleMembership.exists_int_smul_mem ..)

theorem vecMulVec_mem {E : Type} [Field E] [NumberField E] {n d : ℕ} {LX : Submodule (𝓞 E) (Fin n → E)}
    {LY : Submodule (𝓞 E) (Fin d → E)} (sX : Finset LX) (hsX : Submodule.span ℤ (sX : Set LX) = ⊤) (sY : Finset LY)
    (hsY : Submodule.span ℤ (sY : Set LY) = ⊤) (H : AddSubgroup (Matrix (Fin n) (Fin d) E))
    (hH : ∀ x ∈ sX, ∀ y ∈ sY, vecMulVec (x : Fin n → E) (y : Fin d → E) ∈ H) :
    ∀ x ∈ LX, ∀ y ∈ LY, vecMulVec x y ∈ H := by
  intro x hx y hy
  suffices h : ∀ z : LX, ∀ w : LY, vecMulVec (z : Fin n → E) (w : Fin d → E) ∈ H from h ⟨x, hx⟩ ⟨y, hy⟩
  intro z w
  have hz : z ∈ Submodule.span ℤ (sX : Set LX) := by rw [hsX]; trivial
  have hw : w ∈ Submodule.span ℤ (sY : Set LY) := by rw [hsY]; trivial
  induction hz using Submodule.span_induction with
  | mem a ha =>
    induction hw using Submodule.span_induction with
    | mem b hb => exact hH a ha b hb
    | zero =>
      have : vecMulVec (a : Fin n → E) ((0 : LY) : Fin d → E) = 0 := by ext; simp [vecMulVec_apply]
      rw [this]; exact H.zero_mem
    | add b c _ _ hb hc => rw [Submodule.coe_add, vecMulVec_add]; exact H.add_mem hb hc
    | smul k b _ hb => rw [Submodule.coe_smul_of_tower, vecMulVec_smul]; exact H.zsmul_mem hb k
  | zero =>
    have : vecMulVec ((0 : LX) : Fin n → E) (w : Fin d → E) = 0 := by ext; simp [vecMulVec_apply]
    rw [this]; exact H.zero_mem
  | add a b _ _ ha hb => rw [Submodule.coe_add, add_vecMulVec]; exact H.add_mem ha hb
  | smul k a _ ha => rw [Submodule.coe_smul_of_tower, smul_vecMulVec]; exact H.zsmul_mem ha k

theorem exists_gen {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : L.IsLattice E) : ∃ s : Finset L, Submodule.span ℤ (s : Set L) = ⊤ := by
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hL.fg
  haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  exact Module.Finite.fg_top

theorem locCo_smul {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (a : AF F) (w : W) :
    GlobalTheory.LatVac.locCo co v (a • w) = GlobalTheory.AdelicU.evFin F v a • GlobalTheory.LatVac.locCo co v w := by
  simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_smul]
  ext k <;> simp [smul_eq_mul, map_mul]

end GlobalTheory.LatOpenCpt

namespace GlobalTheory.LatOpenCpt
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem incM_single {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (i : Fin n) (j : Fin d) (e : E) :
    incM F (Matrix.single i j e) = Matrix.single i j ((1 : AF F) ⊗ₜ[F] e) := by
  ext a b
  simp only [incM, Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> first | rfl | exact map_zero _

theorem single_eq_vecMulVec {E : Type} [Field E] {n d : ℕ} (i : Fin n) (j : Fin d) (e : E) :
    Matrix.single i j e = vecMulVec (Pi.single i e) (Pi.single j 1) := by
  ext a b
  simp only [Matrix.single_apply, vecMulVec_apply, Pi.single_apply]
  split_ifs <;> simp_all

theorem span_top {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    {LX : Submodule (𝓞 E) (Fin n → E)} {LY : Submodule (𝓞 E) (Fin d → E)} (hX : LX.IsLattice E) (hY : LY.IsLattice E)
    {ι : Type} (t : ι → Matrix (Fin n) (Fin d) E)
    (ht : ∀ x ∈ LX, ∀ y ∈ LY, incM F (vecMulVec x y) ∈ Submodule.span (AF F) (Set.range fun i => incM F (t i)))
    (Z : Matrix (Fin n) (Fin d) (AE F E)) : Z ∈ Submodule.span (AF F) (Set.range fun i => incM F (t i)) := by
  set S := Submodule.span (AF F) (Set.range fun i => incM F (t i))
  have hzs : ∀ (k : ℤ) (P : Matrix (Fin n) (Fin d) E), incM F (k • P) = k • incM F P := fun k P => by
    ext a b; simp [incM, map_zsmul]
  have hall : ∀ (x : Fin n → E) (y : Fin d → E), incM F (vecMulVec x y) ∈ S := by
    intro x y
    obtain ⟨m, hm, hmx⟩ := exists_zsmul_mem LX hX x
    obtain ⟨m', hm', hmy⟩ := exists_zsmul_mem LY hY y
    have h1 := ht _ hmx _ hmy
    rw [smul_vecMulVec, vecMulVec_smul, smul_smul, hzs] at h1
    have hk : ((m * m' : ℤ) : F) ≠ 0 := Int.cast_ne_zero.mpr (mul_ne_zero hm hm')
    have := S.smul_mem (algebraMap F (AF F) ((m * m' : ℤ) : F)⁻¹) h1
    rwa [← Int.cast_smul_eq_zsmul (AF F), smul_smul, ← map_intCast (algebraMap F (AF F)), ← map_mul,
      inv_mul_cancel₀ hk, map_one, one_smul] at this
  have hsingle : ∀ (i : Fin n) (j : Fin d) (z : AE F E), Matrix.single i j z ∈ S := by
    intro i j z
    induction z using TensorProduct.induction_on with
    | zero => rw [Matrix.single_zero]; exact S.zero_mem
    | tmul a e =>
      have h := S.smul_mem a (hall (Pi.single i e) (Pi.single j 1))
      rw [← single_eq_vecMulVec, incM_single, Matrix.smul_single, TensorProduct.smul_tmul', smul_eq_mul, mul_one] at h
      exact h
    | add z z' hz hz' => rw [Matrix.single_add]; exact S.add_mem hz hz'
  rw [Matrix.matrix_eq_sum_single Z]
  exact S.sum_mem fun i _ => S.sum_mem fun j _ => hsingle i j (Z i j)

theorem main : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n)
    (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X Y,
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        M.co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k))) →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F,
      IsOpen (((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v).map (GlobalTheory.LatVac.locCo M.co v) :
        AddSubgroup ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))) : Set ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))) ∧
      IsCompact (((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v).map (GlobalTheory.LatVac.locCo M.co v) :
        AddSubgroup ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))) : Set ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))) := by
  intro F E _ _ _ _ _ σ B n d X Y r s r' s' hX hY M _ v
  obtain ⟨sX, hsX⟩ := exists_gen X.L hX.lat
  obtain ⟨sY, hsY⟩ := exists_gen Y.L hY.lat
  let ι := ↥sX × ↥sY
  let t : ι → Matrix (Fin n) (Fin d) E := fun i => vecMulVec ((i.1 : X.L) : Fin n → E) ((i.2 : Y.L) : Fin d → E)
  let ρ : ι → (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) := fun i => GlobalTheory.LatVac.locCo M.co v (incM F (t i))
  let φ : (ι → Fv F v) →ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) :=
    { toFun := fun f => ∑ i, f i • ρ i
      map_add' := fun f g => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c f => by simp [Finset.smul_sum, smul_smul] }
  have hφ : ∀ f, φ f = ∑ i, f i • ρ i := fun f => rfl
  let Opi : AddSubgroup (ι → Fv F v) := AddSubgroup.pi Set.univ fun _ => (v.adicCompletionIntegers F).toSubring.toAddSubgroup
  have hO : ∀ f, f ∈ Opi ↔ ∀ i, f i ∈ v.adicCompletionIntegers F := fun f => by
    simp only [Opi, AddSubgroup.mem_pi, Set.mem_univ, true_implies]; rfl
  set Λ := (latAtV X Y v).map (GlobalTheory.LatVac.locCo M.co v) with hΛdef
  have hgen : ∀ x ∈ X.L, ∀ y ∈ Y.L, ∀ a : Fv F v, a ∈ v.adicCompletionIntegers F →
      a • GlobalTheory.LatVac.locCo M.co v (incM F (vecMulVec x y)) ∈ Λ := by
    intro x hx y hy a ha
    refine ⟨GlobalTheory.LatVac.liftV v a • incM F (vecMulVec x y), AddSubgroup.subset_closure
      ⟨GlobalTheory.LatVac.liftV v a, GlobalTheory.LatVac.at_liftV v a, by rw [GlobalTheory.LatVac.evFin_liftV]; exact ha, x, hx, y, hy, rfl⟩, ?_⟩
    rw [locCo_smul, GlobalTheory.LatVac.evFin_liftV]
  have hle1 : Opi.map φ.toAddMonoidHom ≤ Λ := by
    rintro _ ⟨f, hf, rfl⟩
    replace hf := (hO _).1 hf
    show ∑ i, f i • ρ i ∈ Λ
    exact Λ.sum_mem fun i _ => hgen _ (i.1 : X.L).2 _ (i.2 : Y.L).2 _ (hf i)
  have hsmul : ∀ a ∈ v.adicCompletionIntegers F, ∀ w ∈ Opi.map φ.toAddMonoidHom, a • w ∈ Opi.map φ.toAddMonoidHom := by
    rintro a ha _ ⟨f, hf, rfl⟩
    replace hf := (hO _).1 hf
    exact ⟨a • f, (hO _).2 fun i => mul_mem ha (hf i), (φ.map_smul a f)⟩
  have hρ : ∀ x ∈ X.L, ∀ y ∈ Y.L,
      GlobalTheory.LatVac.locCo M.co v (incM F (vecMulVec x y)) ∈ Opi.map φ.toAddMonoidHom := by
    let rA : Matrix (Fin n) (Fin d) E →+ (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) :=
      (GlobalTheory.LatVac.locCo M.co v).comp (AddMonoidHom.mapMatrix (inclR (F := F) (AF F)).toAddMonoidHom)
    refine vecMulVec_mem sX hsX sY hsY ((Opi.map φ.toAddMonoidHom).comap rA) ?_
    intro x hx y hy
    refine ⟨Pi.single (⟨x, hx⟩, ⟨y, hy⟩) 1, (hO _).2 fun i => ?_, ?_⟩
    · by_cases h : i = (⟨x, hx⟩, ⟨y, hy⟩)
      · rw [h]; simp
      · simp [Pi.single_apply, h]
    · show ∑ i, (Pi.single ((⟨x, hx⟩, ⟨y, hy⟩) : ι) (1 : Fv F v) : ι → Fv F v) i • ρ i = _
      rw [Finset.sum_eq_single ((⟨x, hx⟩, ⟨y, hy⟩) : ι) (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
      simp only [Pi.single_eq_same, one_smul]
      rfl
  have hle2 : Λ ≤ Opi.map φ.toAddMonoidHom := by
    rw [hΛdef, AddSubgroup.map_le_iff_le_comap, latAtV, AddSubgroup.closure_le]
    rintro _ ⟨a, -, ha, x, hx, y, hy, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, locCo_smul]
    exact hsmul _ ha _ (hρ x hx y hy)
  have hΛ : Λ = Opi.map φ.toAddMonoidHom := le_antisymm hle2 hle1
  have hsurj : ∀ u, ∃ f, φ f = u := by
    intro u
    let U : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
      (fun k => GlobalTheory.LatVac.liftV v (u.1 k), fun k => GlobalTheory.LatVac.liftV v (u.2 k))
    have ht : ∀ x ∈ X.L, ∀ y ∈ Y.L, incM F (vecMulVec x y) ∈ Submodule.span (AF F) (Set.range fun i => incM F (t i)) :=
      vecMulVec_mem sX hsX sY hsY ((Submodule.span (AF F) (Set.range fun i => incM F (t i))).toAddSubgroup.comap
        (AddMonoidHom.mapMatrix (inclR (F := F) (AF F)).toAddMonoidHom)) (fun x hx y hy => Submodule.subset_span ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩)
    have hZ := span_top hX.lat hY.lat t ht (M.co.e.symm U)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hZ
    refine ⟨fun i => GlobalTheory.AdelicU.evFin F v (c i), ?_⟩
    rw [hφ]
    have hu : GlobalTheory.LatVac.locCo M.co v (M.co.e.symm U) = u := by
      ext k <;> simp [GlobalTheory.LatVac.locCo, U, GlobalTheory.LatVac.evFin_liftV]
    rw [← hu, ← hc, map_sum]
    exact Finset.sum_congr rfl fun i _ => (locCo_smul _ _ _ _).symm
  have hOc : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) := PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v
  have hOo : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hφc : Continuous φ := by
    rw [show (φ : (ι → Fv F v) → _) = fun f => ∑ i, f i • ρ i from rfl]
    exact continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const
  have hset : ((Opi.map φ.toAddMonoidHom : AddSubgroup _) : Set _) =
      φ '' Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext w
    simp only [AddSubgroup.coe_map, Set.mem_image, SetLike.mem_coe, hO, Set.mem_pi, Set.mem_univ, true_implies]
    rfl
  choose f1 hf1 using fun k : Fin n × Fin d => hsurj (Pi.single k 1, 0)
  choose f2 hf2 using fun k : Fin n × Fin d => hsurj (0, Pi.single k 1)
  let sec : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) → ι → Fv F v :=
    fun u => ∑ k, u.1 k • f1 k + ∑ k, u.2 k • f2 k
  have hsec : ∀ u, φ (sec u) = u := by
    intro u
    simp only [sec, map_add, map_sum, map_smul, hf1, hf2]
    ext k <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  have hsc : Continuous sec :=
    (continuous_finset_sum _ fun k _ => ((continuous_apply k).comp continuous_fst).smul continuous_const).add
      (continuous_finset_sum _ fun k _ => ((continuous_apply k).comp continuous_snd).smul continuous_const)
  constructor
  · apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
    have hU : IsOpen (sec ⁻¹' Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) :=
      (isOpen_set_pi Set.finite_univ fun _ _ => hOo).preimage hsc
    have h0 : (0 : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) ∈
        sec ⁻¹' Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
      intro i _; simp [sec]
    refine Filter.mem_of_superset (hU.mem_nhds h0) ?_
    intro u hu
    rw [SetLike.mem_coe, hΛ]
    exact ⟨sec u, (hO _).2 fun i => hu i (Set.mem_univ _), hsec u⟩
  · rw [hΛ, hset]
    exact (isCompact_univ_pi fun _ => hOc).image hφc

end GlobalTheory.LatOpenCpt
