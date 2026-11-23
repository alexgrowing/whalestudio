import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertSph.Invert
open GlobalTheory.InertLocField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem at_of_mem {d : ℕ} {W : Spc F E d} {v : Pl F} {z : Fin d → AE F E} (hz : z ∈ latAt W v) (i : Fin d) :
    At (evFin F v) (z i) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, -, y, -, rfl⟩ := hz
    intro u hu
    rw [Pi.smul_apply, smul_smul, ← smul_eq_mul u a, ha u hu, zero_smul]
  | zero => intro u _; exact smul_zero u
  | add x y _ _ hx hy => intro u hu; rw [Pi.add_apply, smul_add, hx u hu, hy u hu, add_zero]
  | neg x _ hx => intro u hu; rw [Pi.neg_apply, smul_neg, hx u hu, neg_zero]

theorem liftT_evT_of_at {v : Pl F} {x : AE F E} (hx : At (evFin F v) x) : liftT E v (evT E v x) = x := by
  obtain ⟨y, rfl⟩ := (at_iff v x).1 hx
  rw [evT_liftT]

theorem liftT_smul (v : Pl F) (t : Fv F v) (y : Fv F v ⊗[F] E) :
    liftT E v (t • y) = GlobalTheory.LatVac.liftV v t • liftT E v y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [TensorProduct.smul_tmul', liftT_tmul, liftT_tmul, smul_eq_mul, liftV_mul, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

theorem evT_smul (v : Pl F) (a : AF F) (x : AE F E) : evT E v (a • x) = evFin F v a • evT E v x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b e =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    show evFin F v (a * b) ⊗ₜ[F] e = evFin F v a • (evFin F v b ⊗ₜ[F] e)
    rw [map_mul, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

theorem smul_mem {d : ℕ} {W : Spc F E d} {v : Pl F} {t : Fv F v} (ht : t ∈ v.adicCompletionIntegers F)
    {z : Fin d → AE F E} (hz : z ∈ latAt W v) : GlobalTheory.LatVac.liftV v t • z ∈ latAt W v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a', ha', hv, y, hy, rfl⟩ := hz
    rw [smul_smul]
    refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v t * a', ?_, ?_, y, hy, rfl⟩
    · intro u hu
      rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a', ha' u hu, mul_zero]
    · rw [map_mul, GlobalTheory.LatVac.evFin_liftV]
      exact mul_mem ht hv
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem mul_liftT (v : Pl F) (x : AE F E) (y : Fv F v ⊗[F] E) :
    x * liftT E v y = liftT E v (evT E v x * y) := by
  have h1 : liftT E v y = GlobalTheory.LatVac.liftV v 1 • liftT E v y := by
    rw [liftV_one_smul, evT_liftT]
  calc x * liftT E v y = GlobalTheory.LatVac.liftV v 1 • (x * liftT E v y) := by rw [← mul_smul_comm, ← h1]
    _ = (GlobalTheory.LatVac.liftV v 1 • x) * liftT E v y := by rw [smul_mul_assoc]
    _ = liftT E v (evT E v x * y) := by rw [liftV_one_smul, liftT_mul]

theorem mulVec_liftT {d : ℕ} (v : Pl F) (X : Matrix (Fin d) (Fin d) (AE F E)) (u : Fin d → Fv F v ⊗[F] E) :
    X *ᵥ (fun i => liftT E v (u i)) = fun i => liftT E v (((X.map (evT E v)) *ᵥ u) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, map_sum, mul_liftT, Matrix.map_apply]

end GlobalTheory.InertSph.Invert

noncomputable section
namespace GlobalTheory.InertSph.Invert
open GlobalTheory.InertLocField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def latV {d : ℕ} (W : Spc F E d) (v : Pl F) : Submodule (v.adicCompletionIntegers F) (Fin d → Fv F v ⊗[F] E) where
  carrier := {u | (fun i => liftT E v (u i)) ∈ latAt W v}
  add_mem' := by
    intro a b ha hb
    have ha' : (fun i => liftT E v (a i)) ∈ latAt W v := ha
    have hb' : (fun i => liftT E v (b i)) ∈ latAt W v := hb
    show (fun i => liftT E v ((a + b) i)) ∈ latAt W v
    convert add_mem ha' hb' using 1
    funext i
    simp
  zero_mem' := by
    show (fun i => liftT E v ((0 : Fin d → Fv F v ⊗[F] E) i)) ∈ latAt W v
    convert zero_mem (latAt W v) using 1
    funext i
    simp
  smul_mem' := by
    intro r u hu
    show (fun i => liftT E v ((r : Fv F v) • u i)) ∈ latAt W v
    simp_rw [liftT_smul]
    exact smul_mem r.2 hu

theorem mem_latV {d : ℕ} {W : Spc F E d} {v : Pl F} {u : Fin d → Fv F v ⊗[F] E} :
    u ∈ latV W v ↔ (fun i => liftT E v (u i)) ∈ latAt W v := Iff.rfl

theorem evT_mem_latV {d : ℕ} {W : Spc F E d} {v : Pl F} {z : Fin d → AE F E} (hz : z ∈ latAt W v) :
    (fun i => evT E v (z i)) ∈ latV W v := by
  rw [mem_latV]
  convert hz using 1
  funext i
  exact liftT_evT_of_at (at_of_mem hz i)

theorem natCast_mem_maximalIdeal (v : Pl F) {p : ℕ} (hp : (p : 𝓞 F) ∈ v.asIdeal) :
    (p : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have hval : Valued.v (algebraMap F (Fv F v) ((p : 𝓞 F) : F)) = v.valuation F ((p : 𝓞 F) : F) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  have hlt : v.valuation F ((p : 𝓞 F) : F) < 1 := (v.valuation_lt_one_iff_mem _).2 hp
  have hpF : algebraMap F (Fv F v) ((p : 𝓞 F) : F) = ((p : v.adicCompletionIntegers F) : Fv F v) := by
    push_cast
    rfl
  rw [hpF] at hval
  have h1 : ((p : v.adicCompletionIntegers F) : Fv F v) * (w : Fv F v) = 1 := by
    rw [← Subring.coe_mul, hw]
    rfl
  have h2 : Valued.v (w : Fv F v) ≤ 1 := w.2
  have h3 := congrArg Valued.v h1
  rw [map_mul, map_one, hval] at h3
  have h4 : v.valuation F ((p : 𝓞 F) : F) * Valued.v (w : Fv F v) < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right' h2) hlt
  exact absurd h3 h4.ne

theorem latV_le {d : ℕ} {W : Spc F E d} {v : Pl F} {p : ℕ} (hp : (p : 𝓞 F) ∈ v.asIdeal) (hfg : (latV W v).FG)
    (M : Matrix (Fin d) (Fin d) (AE F E))
    (hsurj : ∀ z ∈ latAt W v, ∃ y ∈ latAt W v, ∃ y' ∈ latAt W v, z = M *ᵥ y + p • y') :
    ∀ u ∈ latV W v, ∃ y ∈ latV W v, u = (M.map (evT E v)) *ᵥ y := by
  let f : (Fin d → Fv F v ⊗[F] E) →ₗ[v.adicCompletionIntegers F] (Fin d → Fv F v ⊗[F] E) :=
    { toFun := fun y => (M.map (evT E v)) *ᵥ y
      map_add' := Matrix.mulVec_add _
      map_smul' := fun r y => Matrix.mulVec_smul _ _ _ }
  have hJ : Ideal.span {(p : v.adicCompletionIntegers F)} ≤ (⊥ : Ideal (v.adicCompletionIntegers F)).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le, Set.singleton_subset_iff]
    exact natCast_mem_maximalIdeal v hp
  have key := Submodule.le_of_le_smul_of_le_jacobson_bot (N := (latV W v).map f) hfg hJ ?_
  · intro u hu
    obtain ⟨y, hy, e⟩ := Submodule.mem_map.1 (key hu)
    exact ⟨y, hy, e.symm⟩
  intro u hu
  obtain ⟨y, hy, y', hy', e⟩ := hsurj _ hu
  have hyv := evT_mem_latV hy
  have hyv' := evT_mem_latV hy'
  have hy_eq : y = fun i => liftT E v (evT E v (y i)) := funext fun i => (liftT_evT_of_at (at_of_mem hy i)).symm
  rw [hy_eq, mulVec_liftT] at e
  have hu' : u = f (fun i => evT E v (y i)) + (p : v.adicCompletionIntegers F) • fun i => evT E v (y' i) := by
    funext i
    have := congrArg (fun z => evT E v (z i)) e
    simp only [Pi.add_apply, Pi.smul_apply, map_add, map_nsmul, evT_liftT] at this
    rw [this, Pi.add_apply, Pi.smul_apply, Nat.cast_smul_eq_nsmul]
    rfl
  rw [hu']
  exact Submodule.add_mem_sup (Submodule.mem_map_of_mem hyv)
    (Submodule.smul_mem_smul (Ideal.subset_span rfl) hyv')

end GlobalTheory.InertSph.Invert

noncomputable section
namespace GlobalTheory.InertSph.Invert
open GlobalTheory.InertLocField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def oneT (v : Pl F) (d : ℕ) : (Fin d → E) →ₗ[F] (Fin d → Fv F v ⊗[F] E) :=
  LinearMap.pi fun i => (TensorProduct.mk F (Fv F v) E 1).comp (LinearMap.proj i)

theorem oneT_apply (v : Pl F) {d : ℕ} (x : Fin d → E) (i : Fin d) : oneT v d x i = (1 : Fv F v) ⊗ₜ[F] x i := rfl

theorem oneT_mem {d : ℕ} {W : Spc F E d} (v : Pl F) {y : Fin d → E} (hy : y ∈ W.L) : oneT v d y ∈ latV W v := by
  rw [mem_latV]
  refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v 1, GlobalTheory.LatVac.at_liftV v 1,
    by rw [GlobalTheory.LatVac.evFin_liftV]; exact one_mem _, y, hy, ?_⟩
  funext i
  rw [oneT_apply, liftT_tmul, Pi.smul_apply, show inclR (F := F) (AF F) (y i) = (1 : AF F) ⊗ₜ[F] y i from rfl,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem latV_fg {d : ℕ} {W : Spc F E d} (hL : W.L.IsLattice E) (v : Pl F) : (latV W v).FG := by
  obtain ⟨G, hG⟩ := (hL.fg.restrictScalars (R := ℤ))
  let φ : (Fin d → E) →ₗ[ℤ] (Fin d → Fv F v ⊗[F] E) := (oneT v d).restrictScalars ℤ
  have hφ : ∀ y ∈ W.L, oneT v d y ∈ Submodule.span (v.adicCompletionIntegers F) (oneT v d '' G) := by
    intro y hy
    have hy' : y ∈ Submodule.span ℤ (G : Set (Fin d → E)) := by rw [hG]; exact hy
    have h1 : φ y ∈ (Submodule.span ℤ (G : Set (Fin d → E))).map φ := Submodule.mem_map_of_mem hy'
    rw [Submodule.map_span] at h1
    exact Submodule.span_le_restrictScalars ℤ _ _ h1
  classical
  refine ⟨G.image (oneT v d), le_antisymm ?_ ?_⟩
  · rw [Finset.coe_image, Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    have hg' : g ∈ W.L.restrictScalars ℤ := hG ▸ Submodule.subset_span hg
    exact oneT_mem v hg'
  · intro u hu
    rw [Finset.coe_image]
    have key : ∀ z ∈ latAt W v, (fun i => evT E v (z i)) ∈
        Submodule.span (v.adicCompletionIntegers F) (oneT v d '' G) := by
      intro z hz
      induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, -, haO, y, hy, rfl⟩ := hz
        have e : (fun i => evT E v ((a • fun i => inclR (F := F) (AF F) (y i)) i)) =
            (⟨evFin F v a, haO⟩ : v.adicCompletionIntegers F) • oneT v d y := by
          funext i
          rw [Pi.smul_apply, evT_smul, Pi.smul_apply, oneT_apply]
          show evFin F v a • evT E v ((1 : AF F) ⊗ₜ[F] y i) = evFin F v a • ((1 : Fv F v) ⊗ₜ[F] y i)
          congr 1
        rw [e]
        exact Submodule.smul_mem _ _ (hφ y hy)
      | zero =>
        convert zero_mem (Submodule.span (v.adicCompletionIntegers F) (oneT v d '' (G : Set (Fin d → E)))) using 1
        funext i; simp
      | add x y _ _ hx hy =>
        convert add_mem hx hy using 1
        funext i; simp
      | neg x _ hx =>
        convert neg_mem hx using 1
        funext i; simp
    convert key _ hu using 1
    funext i
    rw [evT_liftT]

end GlobalTheory.InertSph.Invert

noncomputable section
namespace GlobalTheory.InertSph.Invert
open GlobalTheory.InertLocField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mulVec_surj {d : ℕ} {W : Spc F E d} (hL : W.L.IsLattice E) (v : Pl F)
    (Mv : Matrix (Fin d) (Fin d) (Fv F v ⊗[F] E)) (h : ∀ u ∈ latV W v, ∃ y, u = Mv *ᵥ y) :
    Function.Surjective (Mv *ᵥ ·) := by
  let T := LinearMap.range (Matrix.mulVecLin Mv)
  let S : Submodule E (Fin d → E) :=
    { carrier := {x | oneT v d x ∈ T}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
        exact add_mem ha hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq, map_zero]
        exact zero_mem _
      smul_mem' := fun e x hx => by
        have he : oneT v d (e • x) = ((1 : Fv F v) ⊗ₜ[F] e) • oneT v d x := by
          funext i
          rw [oneT_apply, Pi.smul_apply, Pi.smul_apply, oneT_apply, smul_eq_mul, smul_eq_mul,
            Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [he]
        exact T.smul_mem _ hx }
  have hLS : Submodule.span E (W.L : Set (Fin d → E)) ≤ S := by
    rw [Submodule.span_le]
    intro y hy
    obtain ⟨y', e⟩ := h _ (oneT_mem v hy)
    exact ⟨y', e.symm⟩
  have hT : ∀ x, oneT v d x ∈ T := fun x => hLS (by rw [hL.span_eq_top]; trivial)
  have hsingle : ∀ (i : Fin d) (b : Fv F v ⊗[F] E), Pi.single i b ∈ T := by
    intro i b
    induction b using TensorProduct.induction_on with
    | zero => rw [Pi.single_zero]; exact zero_mem _
    | add x y hx hy => rw [Pi.single_add]; exact add_mem hx hy
    | tmul t e =>
      have he : Pi.single i (t ⊗ₜ[F] e) = (t ⊗ₜ[F] (1 : E)) • oneT v d (Pi.single i e) := by
        funext j
        rw [Pi.smul_apply, oneT_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        by_cases hj : j = i
        · subst hj; simp
        · simp [Pi.single_apply, hj]
      rw [he]
      exact T.smul_mem _ (hT _)
  intro w
  have hw : w ∈ T := by
    rw [← Finset.univ_sum_single w]
    exact sum_mem fun i _ => hsingle i (w i)
  obtain ⟨y, hy⟩ := hw
  exact ⟨y, hy⟩

theorem mat_ext {d : ℕ} (v : Pl F) {X Y : Matrix (Fin d) (Fin d) (AE F E)} (h1 : X.map (evT E v) = Y.map (evT E v))
    (h2 : (1 - GlobalTheory.LatVac.liftV v 1 : AF F) • X = (1 - GlobalTheory.LatVac.liftV v 1 : AF F) • Y) : X = Y := by
  ext i j
  have a := congrFun (congrFun h1 i) j
  have b := congrFun (congrFun h2 i) j
  simp only [Matrix.map_apply, Matrix.smul_apply] at a b
  calc X i j = (1 - GlobalTheory.LatVac.liftV v 1 : AF F) • X i j + GlobalTheory.LatVac.liftV v 1 • X i j := by
        rw [sub_smul, one_smul, sub_add_cancel]
    _ = (1 - GlobalTheory.LatVac.liftV v 1 : AF F) • Y i j + GlobalTheory.LatVac.liftV v 1 • Y i j := by
        rw [b, liftV_one_smul, liftV_one_smul, a]
    _ = Y i j := by rw [sub_smul, one_smul, sub_add_cancel]

end GlobalTheory.InertSph.Invert

noncomputable section
namespace GlobalTheory.InertSph
open GlobalTheory.InertLocField GlobalTheory.InertSph.Invert

theorem exists_inv_keeps_latAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (W : Spc F E d),
    W.L.IsLattice E → ∀ (v : Pl F) (p : ℕ), (p : 𝓞 F) ∈ v.asIdeal → ∀ c : AF F, IsUnit c →
    ∀ M : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) (M - c • (1 : Matrix (Fin d) (Fin d) (AE F E))) →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, ∃ y ∈ GlobalTheory.InertSph.latAt W v, ∃ y' ∈ GlobalTheory.InertSph.latAt W v, z = M *ᵥ y + p • y') →
    ∃ M' : Matrix (Fin d) (Fin d) (AE F E), M * M' = 1 ∧ M' * M = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt W v, M' *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  intro F E _ _ _ _ _ d W hL v p hp c hc M hMc _ hsurj
  have hN := latV_le hp (latV_fg hL v) M hsurj
  have hS := mulVec_surj hL v (M.map (evT E v)) (fun u hu => by
    obtain ⟨y, -, e⟩ := hN u hu
    exact ⟨y, e⟩)
  have hdet : IsUnit (M.map (evT E v)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.mulVec_surjective_iff_isUnit.1 hS)
  set Nv := (M.map (evT E v))⁻¹ with hNv
  set s : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hs
  have hs0 : evFin F v s = 0 := evFin_one_sub v
  have hss : s * s = s := by
    have he : GlobalTheory.LatVac.liftV v (1 : Fv F v) * GlobalTheory.LatVac.liftV v 1 = GlobalTheory.LatVac.liftV v 1 := by
      rw [← liftV_mul, mul_one]
    rw [hs, sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  let M' : Matrix (Fin d) (Fin d) (AE F E) :=
    ((↑hc.unit⁻¹ : AF F) * s) • (1 : Matrix (Fin d) (Fin d) (AE F E)) + Nv.map (liftT E v)
  have hM'v : M'.map (evT E v) = Nv := by
    ext i j
    simp only [M', Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_add, evT_smul, map_mul, hs0,
      mul_zero, zero_smul, zero_add, evT_liftT]
  have hsM : s • M = (s * c) • (1 : Matrix (Fin d) (Fin d) (AE F E)) := by
    have := hMc s hs0
    rw [smul_sub, sub_eq_zero] at this
    rw [this, smul_smul]
  have hmul : M * M' = 1 := by
    apply mat_ext v
    · have h1 : (M * M').map (evT E v) = M.map (evT E v) * M'.map (evT E v) := by
        ext i j
        simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]
      rw [h1, hM'v, hNv, Matrix.mul_nonsing_inv _ hdet]
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.one_apply, hij]
    · rw [← hs, ← Matrix.smul_mul, hsM, Matrix.smul_mul, Matrix.one_mul]
      simp only [M', smul_add, smul_smul]
      have h0 : (s * c) • Nv.map (liftT E v) = 0 := by
        ext i j
        rw [Matrix.smul_apply, Matrix.map_apply, mul_comm, mul_smul, at_liftT v _ s hs0, smul_zero, Matrix.zero_apply]
      rw [h0, add_zero]
      congr 1
      rw [mul_assoc, ← mul_assoc c, hc.mul_val_inv, one_mul, hss]
  refine ⟨M', hmul, mul_eq_one_comm.1 hmul, fun z hz => ?_⟩
  obtain ⟨y, hy, hu⟩ := hN _ (evT_mem_latV hz)
  have hz' : z = fun i => liftT E v (evT E v (z i)) := funext fun i => (liftT_evT_of_at (at_of_mem hz i)).symm
  rw [hz', mulVec_liftT, hM'v]
  have : (fun i => evT E v (z i)) = (M.map (evT E v)) *ᵥ y := hu
  rw [this, Matrix.mulVec_mulVec, hNv, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  exact hy

end GlobalTheory.InertSph
