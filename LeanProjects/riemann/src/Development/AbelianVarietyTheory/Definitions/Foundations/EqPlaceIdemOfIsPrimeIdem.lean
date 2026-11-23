import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalVAlgebraMapMem
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField

noncomputable section

namespace GlobalTheory.AdelicU.Supp

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

omit [NumberField E] in
theorem tens_map_map {R R' R'' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] [CommRing R'']
    [Algebra F R''] (φ : R →ₐ[F] R') (ψ : R' →ₐ[F] R'') (y : R ⊗[F] E) :
    Algebra.TensorProduct.map ψ (AlgHom.id F E) (Algebra.TensorProduct.map φ (AlgHom.id F E) y) =
      Algebra.TensorProduct.map (ψ.comp φ) (AlgHom.id F E) y := by
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]

omit [NumberField E] in
theorem adTens_eq_one' {y : AF F ⊗[F] E} (h1 : ∀ w, compInf F E w y = 1) (h2 : ∀ v, compFin F E v y = 1) : y = 1 := by
  have := GlobalTheory.AutFunCounterexample.tens_inj (F := F) (E := E) (A := Ainf F) (B := Af F) (n := 1) (Matrix.of fun _ _ => y)
    (by
      ext i j
      rw [Subsingleton.elim i j, Matrix.one_apply_eq]
      exact GlobalTheory.AutFunCompare.infTens_ext fun w => (tens_map_map _ _ y).trans ((h1 w).trans (map_one _).symm))
    (by
      ext i j
      rw [Subsingleton.elim i j, Matrix.one_apply_eq]
      exact GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun v =>
        (tens_map_map _ _ y).trans ((h2 v).trans (map_one _).symm))
  exact congrFun (congrFun this 0) 0

theorem mul_idem_iff_mem_range_emb {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (ε : AF F)
    (e0 : ∀ w, evInf F w ε = 0) (e1 : evFin F v ε = 1) (e2 : ∀ u, u ≠ v → evFin F u ε = 0) (g : GAd σ J) :
    (∀ i j, algebraMap (AF F) (AF F ⊗[F] E) ε * ((matHom _ σ J g).1 - 1) i j = ((matHom _ σ J g).1 - 1) i j) ↔
      g ∈ (emb σ J v).range := by
  have c0 : ∀ w, compInf F E w (algebraMap (AF F) (AF F ⊗[F] E) ε) = 0 := fun w => by
    change evInf F w ε ⊗ₜ[F] (1 : E) = 0
    rw [e0, TensorProduct.zero_tmul]
  have c1 : compFin F E v (algebraMap (AF F) (AF F ⊗[F] E) ε) = 1 := by
    change evFin F v ε ⊗ₜ[F] (1 : E) = 1
    rw [e1]; rfl
  have c2 : ∀ u, u ≠ v → compFin F E u (algebraMap (AF F) (AF F ⊗[F] E) ε) = 0 := fun u hu => by
    change evFin F u ε ⊗ₜ[F] (1 : E) = 0
    rw [e2 u hu, TensorProduct.zero_tmul]
  have one : ∀ {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (m : Matrix (Fin n) (Fin n) A),
      m.map φ = 1 ↔ ∀ i j, φ ((m - 1) i j) = 0 := fun φ m => by
    rw [← Matrix.ext_iff]
    refine forall₂_congr fun i j => ?_
    rw [Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.map_apply]
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have pf : ∀ u, proj σ J u g = 1 ↔ ∀ i j, compFin F E u (((matHom _ σ J g).1 - 1) i j) = 0 := fun u =>
    Iff.trans ⟨fun h => congrArg (fun x => (matHom _ σ J x).1) h, fun h => Subtype.ext (Units.ext h)⟩ (one _ _)
  have pa : ∀ w, projArch σ J w g = 1 ↔ ∀ i j, compInf F E w (((matHom _ σ J g).1 - 1) i j) = 0 := fun u =>
    Iff.trans ⟨fun h => congrArg (fun x => (matHom _ σ J x).1) h, fun h => Subtype.ext (Units.ext h)⟩ (one _ _)
  rw [range_emb, mem_atPts, mem_finPts_iff_forall]
  simp only [pf, pa, Finset.mem_singleton]
  constructor
  · intro h
    exact ⟨fun w i j => by rw [← h, map_mul, c0, zero_mul], fun u hu i j => by rw [← h, map_mul, c2 u hu, zero_mul]⟩
  · rintro ⟨h1, h2⟩ i j
    rw [← sub_eq_zero, ← add_eq_right (b := 1)]
    refine adTens_eq_one' (fun w => ?_) fun u => ?_
    · rw [map_add, map_sub, map_mul, h1, map_one]; simp
    · rw [map_add, map_sub, map_mul, map_one]
      by_cases hu : u = v
      · subst hu; rw [c1]; simp
      · rw [h2 u hu]; simp

omit [NumberField E] in

theorem adTens_ext {y z : AF F ⊗[F] E} (h1 : ∀ w, compInf F E w y = compInf F E w z)
    (h2 : ∀ v, compFin F E v y = compFin F E v z) : y = z := by
  rw [← sub_eq_zero, ← add_eq_right (b := 1)]
  exact adTens_eq_one' (fun w => by simp [h1 w]) fun v => by simp [h2 v]

def placeIdem (v : HeightOneSpectrum (𝓞 F)) : AF F := pairA F 0 (singleFin v 1)

section Single

omit [NumberField E]

variable (E) in

def singleTens (v : HeightOneSpectrum (𝓞 F)) : Fv F v ⊗[F] E →ₙ+* AF F ⊗[F] E :=
  GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (R' := AF F) ((LinearMap.inr F (Ainf F) (Af F)).comp (singleFin v))
    fun a b => Prod.ext (mul_zero _).symm (singleFin_mul v a b)

@[simp] theorem compFin_singleTens_self (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) :
    compFin F E v (singleTens E v y) = y := GlobalTheory.AutFunCompare.map_tensNU_self (evFin F v) _ _ (evalV_singleFin_self v) y

theorem compFin_singleTens_ne {v u : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) (y : Fv F v ⊗[F] E) :
    compFin F E u (singleTens E v y) = 0 := GlobalTheory.AutFunCompare.map_tensNU_zero (evFin F u) _ _ (evalV_singleFin_ne h) y

@[simp] theorem compInf_singleTens (w : InfinitePlace F) (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) :
    compInf F E w (singleTens E v y) = 0 := GlobalTheory.AutFunCompare.map_tensNU_zero _ _ _ (fun _ => rfl) y

theorem compFin_one_tmul (v : HeightOneSpectrum (𝓞 F)) (x : E) :
    compFin F E v ((1 : AF F) ⊗ₜ[F] x) = (1 : Fv F v) ⊗ₜ[F] x := congrArg (· ⊗ₜ[F] x) (map_one (evFin F v))

theorem singleTens_one (v : HeightOneSpectrum (𝓞 F)) :
    singleTens E v 1 = algebraMap (AF F) (AF F ⊗[F] E) (placeIdem v) := rfl

theorem singleTens_mul (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) (z : AF F ⊗[F] E) :
    singleTens E v y * z = singleTens E v (y * compFin F E v z) :=
  adTens_ext (fun w => by simp) fun u => by
    by_cases e : u = v
    · subst e; simp
    · simp [compFin_singleTens_ne e]

theorem sigR_singleTens (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (singleTens E v y) = singleTens E v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Single

variable {σ}

def splitIdemAd (h : IsCMExt F E σ) {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) : AF F ⊗[F] E :=
  singleTens E v (splitIdem h τ)

theorem splitIdem_mul_eq (h : IsCMExt F E σ) {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) (y : Fv F v ⊗[F] E) :
    splitIdem h τ * y = (splitProj τ y ⊗ₜ[F] (1 : E)) * splitIdem h τ :=
  split_ext h τ (by simp [splitIdem]) (by simp [splitIdem])

theorem splitIdemAd_mul (h : IsCMExt F E σ) {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) (z : AF F ⊗[F] E) :
    splitIdemAd h τ * z = singleTens E v (splitProj τ (compFin F E v z) ⊗ₜ[F] (1 : E)) * splitIdemAd h τ := by
  rw [splitIdemAd, singleTens_mul, splitIdem_mul_eq, map_mul]

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult GlobalTheory.IdemModTwo
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)}

theorem isPlaceIdem_placeIdem (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : IsPlaceIdem D v (placeIdem v) :=
  ⟨_, rfl, evalV_singleFin_self v 1, fun _ h => evalV_singleFin_ne h 1⟩

theorem isPlaceIdem_iff {ε : AF D.host.F} : IsPlaceIdem D v ε ↔ ε = placeIdem v := by
  refine ⟨?_, fun e => e ▸ isPlaceIdem_placeIdem D v⟩
  rintro ⟨α, rfl, h1, h2⟩
  refine congrArg (pairA _ 0) (af_ext fun u => ?_)
  by_cases e : u = v
  · subst e; rw [h1, evalV_singleFin_self]
  · rw [h2 u e, evalV_singleFin_ne e]

theorem suppF_iff_mem_range {ε : AF D.host.F} (h : IsPlaceIdem D v ε) (g : GA D V) :
    SuppF V (algebraMap (AF D.host.F) (AE D) ε) g ↔ g ∈ (emb D.sp.cm.sig V.gram v).range := by
  obtain ⟨α, rfl, h1, h2⟩ := h
  exact mul_idem_iff_mem_range_emb _ _ v _ (fun _ => rfl) h1 h2 g

theorem suppAt_iff_mem_range {ε : AF D.host.F} (h : IsPlaceIdem D v ε) {e : AE D}
    (he : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) (g : GA D V) :
    SuppAt e V g ↔ g ∈ (emb D.sp.cm.sig V.gram v).range := by
  rw [← suppF_iff_mem_range V h, ← he]; rfl

theorem emb_mem_KsphC (x : GLoc D.sp.cm.sig V.gram v) :
    emb D.sp.cm.sig V.gram v x ∈ KsphC V ∅ ↔ x ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v := by
  rw [KsphC_eq]
  exact ⟨fun h => by simpa using (mem_levelOff.1 h).2.2 v (by simp), emb_mem_levelOff (by simp)⟩

theorem suppF_and_mem_KsphC {ε : AF D.host.F} (h : IsPlaceIdem D v ε) (g : GA D V) :
    (SuppF V (algebraMap (AF D.host.F) (AE D) ε) g ∧ g ∈ KsphC V ∅) ↔
      g ∈ (stabLoc D.sp.cm.sig V.gram (frameLat V) v).map (emb D.sp.cm.sig V.gram v) := by
  rw [suppF_iff_mem_range V h]
  exact ⟨fun ⟨⟨x, e⟩, hk⟩ => ⟨x, (emb_mem_KsphC V x).1 (e ▸ hk), e⟩,
    fun ⟨x, hx, e⟩ => ⟨⟨x, e⟩, e ▸ (emb_mem_KsphC V x).2 hx⟩⟩

theorem fj_singleV (y : Fv D.host.F v) :
    fj D (singleV D.host.F v y) = singleTens D.host.E v (y ⊗ₜ[D.host.F] (1 : D.host.E)) := rfl

theorem pl_eq (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    pl D v = algebraMap (AF D.host.F) (AE D) (placeIdem v) := rfl

theorem splitAt_splitIdemAd (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    SplitAt D v (splitIdemAd (isCMExt_host D) τ) := by
  have h := isCMExt_host D
  refine ⟨?_, ?_, ?_⟩
  · rw [splitIdemAd, ← map_mul]
    exact congrArg _ (split_ext h τ (by simp [splitIdem]) (by simp [splitIdem]))
  · rw [splitIdemAd, cA, sigR_singleTens, ← map_mul, ← map_zero (singleTens D.host.E v)]
    exact congrArg _ (split_ext h τ (by simp [← splitProj_comp]) (by simp))
  · rw [splitIdemAd, cA, sigR_singleTens, ← map_add, sigR_splitIdem, add_sub_cancel]
    rfl

theorem isIdemAt_splitIdemAd (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    IsIdemAt (D := D) (splitIdemAd (isCMExt_host D) τ) (splitPrime τ) := by
  have he := splitAt_splitIdemAd τ
  refine ⟨(isSplitIdem_iff _).2 ⟨v, he⟩, fun x hx => ?_⟩
  have hφ : ∀ y, splitIdemAd (isCMExt_host D) τ * incA D y =
      fj D (singleV D.host.F v (τ y)) * splitIdemAd (isCMExt_host D) τ := fun y => by
    have e1 : compFin D.host.F D.host.E v (incA D y) = (1 : Fv D.host.F v) ⊗ₜ[D.host.F] y := compFin_one_tmul v y
    rw [splitIdemAd_mul, e1, splitProj_tmul, one_mul, fj_singleV]
  have hx0 : Valued.v (τ x) ≠ 0 := by
    rw [Valuation.ne_zero_iff, map_ne_zero]
    exact fun h => hx (Subtype.ext h)
  rw [mem_splitPrime, hφ, GlobalTheory.IdemPrime.mem_iff he, map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 hx0)]

theorem exists_eq_splitIdemAd {e : AE D} (he : SplitAt D v e) :
    ∃ τ : D.host.E →ₐ[D.host.F] Fv D.host.F v, e = splitIdemAd (isCMExt_host D) τ := by
  have h := isCMExt_host D
  obtain ⟨φ, hφ⟩ := GlobalTheory.IdemPrime.exists_hom he
  let τ : D.host.E →ₐ[D.host.F] Fv D.host.F v := { φ with commutes' := GlobalTheory.IdemPrime.hom_algebraMap he hφ }
  refine ⟨τ, ?_⟩
  have h0 : e = singleTens D.host.E v (compFin _ _ v e) := by
    rw [← one_mul (compFin _ _ v e), ← singleTens_mul]
    exact he.pl_mul.symm
  obtain ⟨y, hy⟩ : ∃ y, y = compFin _ _ v e := ⟨_, rfl⟩
  rw [← hy] at h0
  have inj : Function.Injective (singleTens D.host.E v) := Function.LeftInverse.injective (compFin_singleTens_self v)
  have h1 : y + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig y = 1 := inj (by
    rw [map_add, ← sigR_singleTens, ← h0]; exact he.2.2)
  obtain ⟨d, hd⟩ := exists_cm_conj_ne h
  have h2 : y * (1 ⊗ₜ d) = (τ d ⊗ₜ 1) * y := inj (by
    rw [map_mul (singleTens D.host.E v) (τ d ⊗ₜ 1), ← h0]
    refine Eq.trans ?_ (hφ d)
    conv_rhs => rw [h0, singleTens_mul]
    rfl)
  have h3 : splitProj (τ.comp D.sp.cm.sig) y = 0 := by
    have := congrArg (splitProj (τ.comp D.sp.cm.sig)) h2
    rw [map_mul, map_mul, splitProj_tmul, splitProj_tmul, map_one, one_mul, mul_one, mul_comm, ← sub_eq_zero,
      ← sub_mul] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 fun e => hd (τ.toRingHom.injective e))
  have h4 := congrArg (splitProj τ) h1
  rw [map_add, ← splitProj_comp, h3, add_zero, map_one] at h4
  rw [h0]
  exact congrArg _ (split_ext h τ (by simp [splitIdem, h4]) (by simp [splitIdem, h3]))

theorem isSplitIdem_iff_exists {e : AE D} : IsSplitIdem D e ↔
    ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v),
      e = splitIdemAd (isCMExt_host D) τ :=
  (isSplitIdem_iff e).trans (exists_congr fun _ =>
    ⟨exists_eq_splitIdemAd, fun ⟨τ, h⟩ => h ▸ splitAt_splitIdemAd τ⟩)

theorem isIdemAt_iff_exists {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} : IsIdemAt e P ↔
    ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v),
      e = splitIdemAd (isCMExt_host D) τ ∧ P = splitPrime τ := by
  refine ⟨fun h => ?_, by rintro ⟨v, τ, rfl, rfl⟩; exact isIdemAt_splitIdemAd τ⟩
  obtain ⟨v, τ, rfl⟩ := isSplitIdem_iff_exists.1 h.1
  refine ⟨v, τ, rfl, HeightOneSpectrum.ext (Ideal.ext fun x => ?_)⟩
  by_cases hx : x = 0
  · simp [hx]
  · exact (h.2 x hx).trans ((isIdemAt_splitIdemAd τ).2 x hx).symm

theorem suppAt_splitIdemAd (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (g : GA D V) :
    SuppAt (D := D) (splitIdemAd (isCMExt_host D) τ) V g ↔ g ∈ (emb D.sp.cm.sig V.gram v).range :=
  suppAt_iff_mem_range V (isPlaceIdem_placeIdem D v) ((splitAt_splitIdemAd τ).2.2.trans (pl_eq D v)) g

theorem finPart_fj_mem_iff (y : Fv D.host.F v) :
    finPart D (fj D (singleV D.host.F v y)) ∈ intAE D ↔ Valued.v y ≤ 1 := by
  refine ⟨fun h => ?_, fun h => AddSubgroup.subset_closure
    ⟨singleV D.host.F v y, fun u => by
      by_cases e : u = v
      · subst e; exact (evalV_singleFin_self u y).symm ▸ h
      · exact (evalV_singleFin_ne e y).symm ▸ zero_mem _, 1, rfl⟩⟩
  have key : ∀ z ∈ intAE D, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v)
      (AlgHom.id D.host.F D.host.E) z ∈ intLoc D.host.F D.host.E v := fun z hz => by
    induction hz using AddSubgroup.closure_induction with
    | mem z hz => obtain ⟨a, ha, x, rfl⟩ := hz; exact tmul_mem_intLoc (ha v) x
    | zero => rw [map_zero]; exact zero_mem _
    | add _ _ _ _ h h' => rw [map_add]; exact add_mem h h'
    | neg _ _ h => rw [map_neg]; exact neg_mem h
  have h2 := absFin_le_one_of_mem_intLoc (key _ h)
  change absFin _ v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v (singleFin v y) ⊗ₜ (1 : D.host.E)) ≤ 1 at h2
  rw [evalV_singleFin_self, absFin_tmul_one] at h2
  exact Valued.toNormedField.norm_le_one_iff.1 (by exact_mod_cast h2)

theorem eq_placeIdem_of_isPrimeIdem {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} (h : IsPrimeIdem P e f)
    (hv : P.under (𝓞 D.host.F) = v) :
    f = algebraMap (AF D.host.F) (AE D) (placeIdem v) := by
  rcases h with ⟨h, rfl⟩ | ⟨rfl, ⟨u, ε, hε, rfl⟩, h⟩
  · obtain ⟨u, τ, rfl, rfl⟩ := isIdemAt_iff_exists.1 h
    obtain rfl : u = v := (splitPrime_under τ).symm.trans hv
    exact (splitAt_splitIdemAd τ).2.2
  · obtain rfl := isPlaceIdem_iff.1 hε
    suffices u = v by rw [this]
    refine HeightOneSpectrum.ext (Ideal.ext fun t => ?_)
    by_cases ht : t = 0
    · simp [ht]
    have h2 : Valued.v (algebraMap D.host.F (Fv D.host.F u) (algebraMap (𝓞 D.host.F) D.host.F t)) =
        u.valuation D.host.F (algebraMap (𝓞 D.host.F) D.host.F t) := u.valuedAdicCompletion_eq_valuation' _
    have h3 : ∀ s : D.host.F, algebraMap (AF D.host.F) (AE D) (placeIdem u) *
        incA D (algebraMap D.host.F D.host.E s)⁻¹ = fj D (singleV D.host.F u (algebraMap D.host.F _ s)⁻¹) := fun s => by
      have e1 : ∀ y, compFin D.host.F D.host.E u (incA D y) = (1 : Fv D.host.F u) ⊗ₜ[D.host.F] y := compFin_one_tmul u
      rw [← singleTens_one, singleTens_mul, one_mul, e1, ← map_inv₀, ← map_inv₀, tmul_algebraMap_eq, mul_one,
        fj_singleV]
      rfl
    have h0 : u.valuation D.host.F (algebraMap (𝓞 D.host.F) D.host.F t) ≠ 0 := by
      rw [Valuation.ne_zero_iff]; exact fun e => ht (Subtype.ext e)
    rw [← hv]
    change _ ↔ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈ P.asIdeal
    rw [h _ (by simpa using ht), show ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t : 𝓞 D.host.E) : D.host.E) =
        algebraMap D.host.F D.host.E (algebraMap (𝓞 D.host.F) D.host.F t) from rfl, h3, finPart_fj_mem_iff, map_inv₀, h2, not_le,
      one_lt_inv₀ (zero_lt_iff.2 h0)]
    exact (u.valuation_lt_one_iff_mem _).symm

theorem suppF_iff_of_isPrimeIdem {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} (h : IsPrimeIdem P e f)
    (hv : P.under (𝓞 D.host.F) = v) (g : GA D V) :
    SuppF V f g ↔ g ∈ (emb D.sp.cm.sig V.gram v).range := by
  rw [eq_placeIdem_of_isPrimeIdem h hv, suppF_iff_mem_range V (isPlaceIdem_placeIdem D v)]

end Record

end GlobalTheory.AdelicU.Supp

end
