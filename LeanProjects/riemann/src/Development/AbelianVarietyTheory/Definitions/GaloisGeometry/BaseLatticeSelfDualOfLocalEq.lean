import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MemberChainFormsLevelPrimeEqMember
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.SplitIntPI
import Formalism.LocalToGlobal.HermitianColumns.SymAll
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.IntSplitOf

noncomputable section

section

namespace GlobalTheory.Port
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChartsLv

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
  (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))

theorem IsBaseAt.congr {N : ℕ} {B : GL (Fin N) D.host.E} {Lb Lb' : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (h : IsBaseAt X0 u w hg B Lb)
    (e : ∀ w' : HeightOneSpectrum (𝓞 D.host.F), ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal →
      Formalism.L2.Herm.locL w' Lb' = Formalism.L2.Herm.locL w' Lb) : IsBaseAt X0 u w hg B Lb' := by
  intro w' hw t
  rw [e w' hw]
  exact h w' hw t

section Free

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
  (v : HeightOneSpectrum (𝓞 F)) (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)

def rho : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F := (RingHom.fst _ _).comp spl.toRingHom

variable {v spl}

theorem rho_int (hs : SplitInt v spl) (x : E ⊗[F] v.adicCompletion F) (hx : x ∈ intV E v) :
    rho v spl x ∈ v.adicCompletionIntegers F := ((hs x).1 hx).1

theorem mulVec_map_rho (A : Matrix (Fin N) (Fin N) E) (x : Fin N → E) (a : Fin N) :
    ((A.map ((rho v spl).comp (inclE (F := F) (v.adicCompletion F)))) *ᵥ
      fun b => rho v spl (inclE (F := F) (v.adicCompletion F) (x b))) a =
      rho v spl (inclE (F := F) (v.adicCompletion F) ((A *ᵥ x) a)) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, RingHom.comp_apply, map_sum, map_mul]

theorem base_free (hs : SplitInt v spl) (hd : ∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a)) (B : GL (Fin N) E)
    (Λ : Submodule (𝓞 E) (Fin N → E))
    (hΛ : ∀ x, x ∈ Λ ↔ ∀ a, (((B⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x) a ∈ (algebraMap (𝓞 E) E).range)
    (t : Fin N → v.adicCompletion F) :
    (∃ x ∈ Formalism.L2.Herm.locL v Λ, ∀ a, (spl (x a)).1 = t a) ↔
      ∀ a, (((bc ((rho v spl).comp (inclE (F := F) (v.adicCompletion F))) B)⁻¹ : GL (Fin N) (v.adicCompletion F)) :
        Matrix (Fin N) (Fin N) (v.adicCompletion F)).mulVec t a ∈ v.adicCompletionIntegers F := by
  have hinv : (((bc ((rho v spl).comp (inclE (F := F) (v.adicCompletion F))) B)⁻¹ : GL (Fin N) (v.adicCompletion F)) :
      Matrix (Fin N) (Fin N) (v.adicCompletion F)) =
      ((B⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map ((rho v spl).comp (inclE (F := F) (v.adicCompletion F))) := by
    unfold bc
    rw [← map_inv, Units.coe_map]
    rfl

  have hO : ∀ e ∈ (algebraMap (𝓞 E) E).range,
      rho v spl (inclE (F := F) (v.adicCompletion F) e) ∈ v.adicCompletionIntegers F := fun e he =>
    rho_int hs _ (Subring.subset_closure (Or.inl ⟨⟨e, he⟩, rfl⟩))
  have hfst : ∀ s ∈ intV E v, (spl s).1 ∈ v.adicCompletionIntegers F := fun s hs' => ((hs s).1 hs').1
  rw [hinv]
  constructor
  ·
    rintro ⟨x, hx, hxt⟩
    have ht : t = fun b => (spl (x b)).1 := funext fun b => (hxt b).symm
    subst ht
    clear hxt
    unfold Formalism.L2.Herm.locL latS at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      intro a
      show ((((B⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map ((rho v spl).comp (inclE (F := F) (v.adicCompletion F)))) *ᵥ
        fun b => rho v spl (inclE (F := F) (v.adicCompletion F) (z b))) a ∈ v.adicCompletionIntegers F
      rw [mulVec_map_rho]
      exact hO _ ((hΛ z).1 hz a)
    | zero =>
      intro a
      have e : (fun b => (spl ((0 : Fin N → E ⊗[F] v.adicCompletion F) b)).1) = 0 := by
        funext b
        simp
      rw [e, Matrix.mulVec_zero]
      exact zero_mem (v.adicCompletionIntegers F)
    | add x y _ _ ihx ihy =>
      intro a
      have e : (fun b => (spl ((x + y) b)).1) = (fun b => (spl (x b)).1) + (fun b => (spl (y b)).1) := by
        funext b
        simp only [Pi.add_apply, map_add, Prod.fst_add]
      rw [e, Matrix.mulVec_add]
      exact add_mem (ihx a) (ihy a)
    | smul s x _ ih =>
      intro a
      have e : (fun b => (spl ((s • x) b)).1) = (spl (s : E ⊗[F] v.adicCompletion F)).1 • (fun b => (spl (x b)).1) := by
        funext b
        simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul, Prod.fst_mul]
      rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      exact mul_mem (hfst s s.2) (ih a)
  ·
    intro h
    set c : Fin N → v.adicCompletion F := ((B⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map
      ((rho v spl).comp (inclE (F := F) (v.adicCompletion F))) *ᵥ t with hc
    have hcm : ∀ b, (1 : E) ⊗ₜ[F] c b ∈ intV E v := fun b =>
      Subring.subset_closure (Or.inr ⟨⟨c b, h b⟩, rfl⟩)
    have hcol : ∀ b, (fun i => (B : Matrix (Fin N) (Fin N) E) i b) ∈ Λ := by
      intro b
      rw [hΛ]
      intro a
      have e : (((B⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ fun i => (B : Matrix (Fin N) (Fin N) E) i b) a =
          (1 : Matrix (Fin N) (Fin N) E) a b := by
        rw [← Units.inv_mul B, Matrix.mul_apply]
        simp only [Matrix.mulVec, dotProduct]
      rw [e, Matrix.one_apply]
      split_ifs
      · exact ⟨1, map_one _⟩
      · exact ⟨0, map_zero _⟩
    refine ⟨∑ b, (⟨(1 : E) ⊗ₜ[F] c b, hcm b⟩ : intV E v) •
      (fun i => inclE (F := F) (v.adicCompletion F) ((B : Matrix (Fin N) (Fin N) E) i b)), ?_, fun a => ?_⟩
    · unfold Formalism.L2.Herm.locL latS
      exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hcol b, rfl⟩)
    · have key : ((B : Matrix (Fin N) (Fin N) E).map ((rho v spl).comp (inclE (F := F) (v.adicCompletion F))) *ᵥ c) = t := by
        rw [hc, Matrix.mulVec_mulVec, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _),
          Matrix.one_mulVec]
      rw [← key]
      simp only [Finset.sum_apply, Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_sum, map_mul, Prod.fst_sum,
        Prod.fst_mul, hd, Matrix.mulVec, dotProduct, Matrix.map_apply, RingHom.comp_apply]
      refine Finset.sum_congr rfl fun b _ => ?_
      exact mul_comm _ _

end Free

theorem isBaseAt_free {N : ℕ} (B : GL (Fin N) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (hΛ : ∀ x, x ∈ Λ ↔ ∀ a, (((B⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) *ᵥ x) a ∈
      (algebraMap (𝓞 D.host.E) D.host.E).range) : IsBaseAt X0 u w hg B Λ := fun w' h t =>
  base_free (split_integral_completion D.host.F D.host.E w' _ ((X0.g u w hg).spl_alg w' h)) ((X0.g u w hg).spl_alg w' h) B Λ hΛ t

end GlobalTheory.Port
end
section
namespace GlobalTheory.Port

open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChartsLv

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem reGL_symm_rfl {a : ℕ} (R : Type) [CommRing R] (x : GL (Fin a) R) : (Formalism.L2.Forms.reGL rfl R).symm x = x := by
  apply (Formalism.L2.Forms.reGL rfl R).injective
  rw [MulEquiv.apply_symm_apply, Formalism.L2.Forms.reGL_rfl]

theorem free_re {E : Type} [Field E] {a b : ℕ} (h : a = b) (C : GL (Fin b) E) (S : Set E) (x : Fin a → E) :
    (∀ k, ((C : Matrix (Fin b) (Fin b) E) *ᵥ reV h E x) k ∈ S) ↔
      ∀ k, (((((Formalism.L2.Forms.reGL h E).symm C⁻¹)⁻¹ : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) *ᵥ x) k ∈ S := by
  subst h
  rw [reGL_symm_rfl, inv_inv, reV_rfl]

variable {D : D7}

theorem mem_crdLat_iff (i : ℕ) (hi : i ≤ D.R.m) (x : Fin (D.sp.X i).rank → D.host.E) :
    x ∈ Formalism.L2.Herm.crdLat (D.sp.X i) (D.sp.X i).L0 ↔ reV (rankN D i hi) D.host.E x ∈ selfDualLatticeCoords D i hi := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, e⟩
    exact ⟨y, hy, (reV (rankN D i hi) D.host.E).injective e⟩

theorem std_of_C {E : Type} [Field E] (σ : E →+* E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (C : GL (Fin N) E)
    (hC : cT σ (C : Matrix (Fin N) (Fin N) E) * (C : Matrix (Fin N) (Fin N) E) = J) :
    cT σ ((C⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) * J * ((C⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = 1 := by
  have h1 : cT σ ((C⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) * cT σ (C : Matrix (Fin N) (Fin N) E) = 1 := by
    rw [← cT_mul, Units.mul_inv, cT_one]
  calc _ = (cT σ ((C⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) * cT σ (C : Matrix (Fin N) (Fin N) E)) *
        ((C : Matrix (Fin N) (Fin N) E) * ((C⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)) := by
        rw [← hC]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Units.mul_inv, Matrix.one_mul]

variable (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
  (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {i : ℕ} {hi : i + 1 ≤ D.R.m}

theorem baseEx_of (Fo : FormsIn M (i + 1) hi) (Cm : GL (Fin (D.R.N (i + 1))) D.host.E)
    (h1 : cT (sigD D : D.host.E →+* D.host.E) Cm.1 * Cm.1 = gramN D (i + 1) hi)
    (h2 : ∀ x : Fin (D.R.N (i + 1)) → D.host.E, x ∈ selfDualLatticeCoords D (i + 1) hi ↔
      ∀ a, (Cm.1 *ᵥ x) a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range)
    (hL : ChartBaseLatticeEqSelfDualAtP u Fo (D.what₂.places.resChar w)) : BaseEx X0 u w hg Fo := by
  refine ⟨(Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm Cm⁻¹, ?_, fun β => ?_⟩
  · rw [MulEquiv.apply_symm_apply]
    exact std_of_C _ _ Cm h1
  · refine IsBaseAt.congr X0 u w hg (isBaseAt_free X0 u w hg _ (Formalism.L2.Herm.crdLat (D.sp.X (i + 1)) (D.sp.X (i + 1)).L0) fun x => ?_)
      (hL β)
    rw [mem_crdLat_iff (i + 1) hi, h2]
    exact free_re (rankN D (i + 1) hi) Cm _ x

end GlobalTheory.Port

end

section
namespace GlobalTheory.Port

open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ChartsLv

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.L2.Herm
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem locL_mono {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) {Λ Λ' : Submodule (𝓞 E) (Fin n → E)} (h : Λ ≤ Λ') :
    locL v Λ ≤ locL v Λ' :=
  Submodule.span_mono (Set.image_mono h)

theorem natVal_one (v : HeightOneSpectrum (𝓞 F)) (T : ℕ) (hT : (T : 𝓞 F) ∉ v.asIdeal) :
    Valued.v ((T : ℕ) : v.adicCompletion F) = 1 := by
  have h : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (T : 𝓞 F))) =
      v.valuation F (algebraMap (𝓞 F) F (T : 𝓞 F)) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  rw [HeightOneSpectrum.valuation_of_algebraMap, (v.intValuation_eq_one_iff_mem_primeCompl _).2 hT] at h
  have e : algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (T : 𝓞 F)) = ((T : ℕ) : v.adicCompletion F) := by
    rw [map_natCast, map_natCast]
  rwa [e] at h

theorem natInv_mem (v : HeightOneSpectrum (𝓞 F)) (T : ℕ) (hT : (T : 𝓞 F) ∉ v.asIdeal) :
    ((T : ℕ) : v.adicCompletion F)⁻¹ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, natVal_one v T hT, inv_one]

theorem loc_lattice_eq_of_torsion_away {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Λ Λ' : Submodule (𝓞 E) (Fin n → E)) (T : ℕ)
    (hT : (T : 𝓞 F) ∉ v.asIdeal) (h1 : Λ ≤ Λ') (h2 : ∀ y ∈ Λ', (T : E) • y ∈ Λ) : locL v Λ' = locL v Λ := by
  refine le_antisymm ?_ (locL_mono v h1)
  refine Submodule.span_le.2 ?_
  rintro _ ⟨y, hy, rfl⟩
  have hne : ((T : ℕ) : v.adicCompletion F) ≠ 0 := by
    intro h0
    have := natVal_one v T hT
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hc : (1 : E) ⊗ₜ[F] ((T : ℕ) : v.adicCompletion F)⁻¹ ∈ intV E v :=
    Subring.subset_closure (Or.inr ⟨⟨_, natInv_mem v T hT⟩, rfl⟩)
  have hmem : (fun i => inclE (F := F) (v.adicCompletion F) (((T : E) • y) i)) ∈ locL v Λ :=
    Submodule.subset_span ⟨_, h2 y hy, rfl⟩
  have he : (fun i => inclE (F := F) (v.adicCompletion F) (y i)) =
      (⟨_, hc⟩ : intV E v) • (fun i => inclE (F := F) (v.adicCompletion F) (((T : E) • y) i)) := by
    funext i
    show (y i) ⊗ₜ[F] (1 : v.adicCompletion F) =
      ((1 : E) ⊗ₜ[F] ((T : ℕ) : v.adicCompletion F)⁻¹) * (((T : E) * y i) ⊗ₜ[F] (1 : v.adicCompletion F))
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    have h3 : (T : E) * y i = ((T : ℕ) : F) • y i := by
      rw [Algebra.smul_def]; simp
    rw [h3, TensorProduct.smul_tmul, Algebra.smul_def]
    congr 1
    have h4 : algebraMap F (v.adicCompletion F) ((T : ℕ) : F) = ((T : ℕ) : v.adicCompletion F) := by simp
    rw [h4, mul_inv_cancel₀ hne]
  show (fun i => inclE (F := F) (v.adicCompletion F) (y i)) ∈ locL v Λ
  rw [he]
  exact Submodule.smul_mem _ _ hmem

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem reL_symm_reL {a b : ℕ} (h : a = b) {E : Type} [Field E] [NumberField E] (L : Submodule (𝓞 E) (Fin a → E)) :
    reL h.symm (reL h L) = L := by
  subst h
  rw [reL_rfl, reL_rfl]

variable {D : D7}

theorem locL_memCh (H : HermColsCh D) (aT : ∀ u, AtT D u (H.vT u) (H.Fv u)) (hb : SymmetricBaseCompatibility D H aT) (u : D.what₂.Word) (i : ℕ)
    (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (β : H.Ch u i) (v : HeightOneSpectrum (𝓞 D.host.F))
    (hT : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) :
    locL v (H.lev u i h1 hm β).Lb = locL v (crdLat (D.sp.X i) (D.sp.X i).L0) := by
  have hi : IsIntegral ℤ (D.host.conj ((aT u).piU : D.host.E)) :=
    map_isIntegral_int D.host.conj (RingOfIntegers.isIntegral_coe _)
  have e := (hb u ⟨_, hi⟩ rfl).2 i h1 hm β
  rw [← e]
  refine (loc_lattice_eq_of_torsion_away v _ _ (D.mem u).A.T hT le_sup_left fun y hy => ?_).symm
  exact (H.lev u i h1 hm β).Lb_dual y (sup_le (H.lev u i h1 hm β).Lb_int Submodule.smul_le_right hy)

variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {i : ℕ} {hi : i + 1 ≤ D.R.m}

def BaseLatticeSelfDualAbove (Fo : FormsIn M (i + 1) hi) (p : ℕ) : Prop :=
  ∀ (β : Fo.Ch) (w' : HeightOneSpectrum (𝓞 D.host.F)), ((p : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal →
    locL w' (lbOf Fo β) = locL w' (crdLat (D.sp.X (i + 1)) (D.sp.X (i + 1)).L0)

theorem base_lattice_self_dual_of_local_eq (Fo : FormsIn M (i + 1) hi) (p : ℕ) (Lh : Fo.Ch → Submodule (𝓞 D.host.E) (Fin (D.sp.X (i + 1)).rank → D.host.E))
    (hcar : ∀ β, (Fo.K β).lev.Lb = reL (rankN D (i + 1) hi) (Lh β))
    (hL : ∀ β (w' : HeightOneSpectrum (𝓞 D.host.F)), ((p : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal →
      locL w' (Lh β) = locL w' (crdLat (D.sp.X (i + 1)) (D.sp.X (i + 1)).L0)) : BaseLatticeSelfDualAbove Fo p := by
  intro β w' hw
  unfold lbOf
  rw [hcar β, reL_symm_reL]
  exact hL β w' hw

section Mem

variable (cols : ColsTiedSym D)

set_option maxHeartbeats 4000000 in

theorem top_car (u : D.what₂.Word) (j : ℕ) (hj : j ≤ D.R.m) (h : j = D.R.m) (h1 : 1 ≤ j) :
    ∃ β' : cols.herm.base.Ch u j,
      ((cols.forms u).cls j hj (Or.inr h)).lev.Lb = reL (rankN D j hj) (cols.herm.base.lev u j h1 hj β').Lb := by
  subst h
  exact ⟨chM cols.herm.base u, (cols.carM u).Lb_eq⟩

set_option maxHeartbeats 4000000 in

theorem base_lattice_self_dual_of_chain (u : D.what₂.Word) (dt : MemDt (cols.forms u)) (i : ℕ) (hi : i + 1 ≤ D.R.m) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    BaseLatticeSelfDualAbove (formsInMem (cols.forms u) dt i hi) (D.what₂.places.resChar w) := by
  by_cases h : i + 1 = D.R.m
  · rw [formsInMem_top (cols.forms u) dt i hi h]
    obtain ⟨β', hβ⟩ := top_car cols u (i + 1) hi h (one_le i)
    exact base_lattice_self_dual_of_local_eq (formsInOne ((cols.forms u).val (i + 1) hi (Or.inr h)) (dt.top (i + 1) hi h)) _
      (fun _ => (cols.herm.base.lev u (i + 1) (one_le i) hi β').Lb) (fun _ => hβ) fun _ w' hw =>
        locL_memCh cols.herm.base cols.herm.atT cols.herm.baseL u (i + 1) (one_le i) hi β' w'
          (natCast_notMem w' hg.1 hw hg.2.2.2.2.2)
  · have h2 : i + 1 + 1 ≤ D.R.m := by omega
    rw [formsInMem_mid (cols.forms u) dt i hi h2]
    exact base_lattice_self_dual_of_local_eq (formsInMid (cols.forms u) (i + 1) (one_le i) h2 (dt.mid (i + 1) (one_le i) h2)) _
      (fun β => (cols.herm.base.lev u (i + 1) (one_le i) (le_of_succ_m h2) β).Lb)
      (fun β => (cols.carC u (i + 1) (one_le i) h2 β).Lb_eq) fun β w' hw =>
        locL_memCh cols.herm.base cols.herm.atT cols.herm.baseL u (i + 1) (one_le i) (le_of_succ_m h2) β w'
          (natCast_notMem w' hg.1 hw hg.2.2.2.2.2)

end Mem

section Rec

open Formalism.MainNotions

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Dx cX}

end Rec

end GlobalTheory.Port

end

end
