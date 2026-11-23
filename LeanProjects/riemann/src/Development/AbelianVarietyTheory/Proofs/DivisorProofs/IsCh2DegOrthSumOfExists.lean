import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitCokernelCoforkBiprodMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBcFiniteOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullRegCoverIsCInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubmatrixSchurComplementCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantMetricIsometricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalSumPullbackIsometricStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.SecondChernDegreeSum

open Limits VMetric

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem form_zero_left {σ : k →+* ℂ} {E : X.Modules} {r : ℕ} (h : Met p σ E r) {U : X.Opens}
    (t : Γ(E, U)) (y : CxPts p σ) : h.form 0 t y = 0 := by
  simpa using h.form_add_left 0 0 t y

theorem form_zero_right {σ : k →+* ℂ} {E : X.Modules} {r : ℕ} (h : Met p σ E r) {U : X.Opens}
    (t : Γ(E, U)) (y : CxPts p σ) : h.form t 0 y = 0 := by
  rw [← h.conj_form, form_zero_left, map_zero]

section Seq

open VBExt HermFrame Filter Topology
open GlobalTheory.Twist (resM app_resM)
open scoped ComplexOrder

variable {S S' : ShortComplex X.Modules} {T : X.Modules} {r m s : ℕ}
  {u₁ : S'.X₁ ⟶ S.X₁} {u₂ : S'.X₂ ⟶ S.X₂} {v : T ⟶ S.X₁}

theorem exists_iso_X₃ (hS : S.ShortExact) (hS' : S'.ShortExact) (w : u₁ ≫ S.f = S'.f ≫ u₂)
    [IsIso (biprod.desc u₁ v)] [IsIso (biprod.desc u₂ (v ≫ S.f))] :
    ∃ φ : S'.X₃ ≅ S.X₃, S'.g ≫ φ.hom = u₂ ≫ S.g := by
  have := hS.epi_g
  have := hS'.epi_g
  have z₁ : S'.f ≫ u₂ ≫ S.g = 0 := by rw [← Category.assoc, ← w, Category.assoc, S.zero, comp_zero]
  have k₁ : u₂ ≫ inv (biprod.desc u₂ (v ≫ S.f)) = biprod.inl := by
    rw [IsIso.comp_inv_eq, biprod.inl_desc]
  have k₂ : (v ≫ S.f) ≫ inv (biprod.desc u₂ (v ≫ S.f)) = biprod.inr := by
    rw [IsIso.comp_inv_eq, biprod.inr_desc]
  have z₂ : S.f ≫ inv (biprod.desc u₂ (v ≫ S.f)) ≫ biprod.fst ≫ S'.g = 0 := by
    rw [← cancel_epi (biprod.desc u₁ v), comp_zero]
    refine biprod.hom_ext' _ _ ?_ ?_
    · rw [biprod.inl_desc_assoc, reassoc_of% w, reassoc_of% k₁, biprod.inl_fst_assoc, S'.zero,
        comp_zero]
    · rw [biprod.inr_desc_assoc, reassoc_of% k₂, biprod.inr_fst_assoc, zero_comp,
        comp_zero]
  refine ⟨⟨hS'.exact.desc _ z₁, hS.exact.desc _ z₂, ?_, ?_⟩, hS'.exact.g_desc _ z₁⟩
  · rw [← cancel_epi S'.g, ShortComplex.Exact.g_desc_assoc, Category.assoc,
      ShortComplex.Exact.g_desc, reassoc_of% k₁, biprod.inl_fst_assoc, Category.comp_id]
  · rw [← cancel_epi S.g, ShortComplex.Exact.g_desc_assoc, Category.assoc, Category.assoc,
      ShortComplex.Exact.g_desc, Category.comp_id, IsIso.inv_comp_eq]
    refine biprod.hom_ext' _ _ ?_ ?_ <;> simp

noncomputable def sumChart [IsIso (biprod.desc u₁ v)] (φ : S'.X₃ ≅ S.X₃)
    (hφ : S'.g ≫ φ.hom = u₂ ≫ S.g) (a : AdaptedChart S' r s) (f : Fin m → Γ(T, a.U))
    (hf : IsFrame f) : AdaptedChart S (r + m) s where
  U := a.U
  e := Sum.elim (fun i => u₁.app a.U (a.e i)) (fun j => v.app a.U (f j)) ∘ finSumFinEquiv.symm
  t j := u₂.app a.U (a.t j)
  he := by
    refine IsFrame.comp_equiv ?_ _
    have h := (isFrame_sumElim (ShortComplex.Splitting.ofHasBinaryBiproduct S'.X₁ T).shortExact
      a.he (t := fun j => (biprod.inr : T ⟶ S'.X₁ ⊞ T).app a.U (f j)) (by
        convert hf using 2 with j
        exact congr(($(biprod.inr_snd (X := S'.X₁) (Y := T))).app a.U (f j)))).map_iso
      (biprod.desc u₁ v)
    convert h using 2 with i
    rcases i with i | j
    · exact congr(($(biprod.inl_desc u₁ v)).app a.U (a.e i)).symm
    · exact congr(($(biprod.inr_desc u₁ v)).app a.U (f j)).symm
  ht := by
    convert a.ht.map_iso φ.hom using 2 with j
    exact congr(($hφ).app a.U (a.t j)).symm

theorem exists_adapted_frame {σ : k →+* ℂ} (hS' : S'.ShortExact) (h₁ : IsVB S'.X₁ r)
    (h₃ : IsVB S'.X₃ s) (hT : IsVB T m) (y : CxPts p σ) : ∃ (a : AdaptedChart S' r s)
      (f : Fin m → Γ(T, a.U)), IsFrame f ∧ y ∈ ptsIn p σ a.U := by
  obtain ⟨a, ha⟩ := Met.exists_adapted hS' h₁ h₃ y
  refine ⟨⟨a.U ⊓ (hT.pick y).U, _, fun j => resM _ inf_le_left (a.t j), a.he.res inf_le_left, ?_⟩,
    _, (hT.pick y).isFrame.res inf_le_right, mem_ptsIn_inf.2 ⟨ha, hT.mem_pick y⟩⟩
  simp only [app_resM]
  exact a.ht.res inf_le_left

theorem gram_sumChart {σ : k →+* ℂ} (hS : S.ShortExact) (w : u₁ ≫ S.f = S'.f ≫ u₂)
    [IsIso (biprod.desc u₁ v)] (φ : S'.X₃ ≅ S.X₃) (hφ : S'.g ≫ φ.hom = u₂ ≫ S.g)
    {h : Met p σ S.X₂ (r + m + s)} {h' : Met p σ S'.X₂ (r + s)}
    (e₁ : ∀ (U : X.Opens) (a b : Γ(S'.X₂, U)), ∀ y ∈ ptsIn p σ U,
      h.form (u₂.app U a) (u₂.app U b) y = h'.form a b y)
    (e₂ : ∀ (U : X.Opens) (a : Γ(S'.X₂, U)) (t : Γ(T, U)), ∀ y ∈ ptsIn p σ U,
      h.form (u₂.app U a) ((v ≫ S.f).app U t) y = 0)
    (a : AdaptedChart S' r s) (f : Fin m → Γ(T, a.U)) (hf : IsFrame f) {y : CxPts p σ}
    (hy : y ∈ ptsIn p σ a.U) :
    let K := h.gram (sumChart (u₁ := u₁) (v := v) φ hφ a f hf).frame y
    let j : Fin r ⊕ Fin s → Fin (r + m) ⊕ Fin s := Sum.map (fun a => finSumFinEquiv (Sum.inl a)) id
    K.submatrix j j = h'.gram a.frame y ∧
      (∀ x (b : Fin m), K (j x) (Sum.inl (finSumFinEquiv (Sum.inr b))) = 0 ∧
        K (Sum.inl (finSumFinEquiv (Sum.inr b))) (j x) = 0) ∧ IsUnit (subGram K).det := by
  intro K j
  have f₁ (x) : (sumChart (u₁ := u₁) (v := v) φ hφ a f hf).frame (j x) = u₂.app a.U (a.frame x) := by
    rcases x with x | x
    · change S.f.app a.U (Sum.elim _ _ (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl x)))) = _
      rw [Equiv.symm_apply_apply]
      exact congr(($w).app a.U (a.e x))
    · rfl
  have f₂ (b : Fin m) : (sumChart (u₁ := u₁) (v := v) φ hφ a f hf).frame
      (Sum.inl (finSumFinEquiv (Sum.inr b))) = (v ≫ S.f).app a.U (f b) := by
    change S.f.app a.U (Sum.elim _ _ (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr b)))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  have z (x) (b : Fin m) : K (j x) (Sum.inl (finSumFinEquiv (Sum.inr b))) = 0 :=
    (congrArg₂ (fun s t => h.form s t y) (f₁ x) (f₂ b)).trans (e₂ _ _ _ y hy)
  refine ⟨Matrix.ext fun x x' => (congrArg₂ (fun s t => h.form s t y) (f₁ x) (f₁ x')).trans
    (e₁ _ _ _ y hy), fun x b => ⟨z x b, ?_⟩,
    (posDef_subGram (h.posDef_gram_frame hS
      (sumChart (u₁ := u₁) (v := v) φ hφ a f hf) hy)).det_pos.ne'.isUnit⟩
  exact (h.conj_form _ _ y).symm.trans ((congrArg (starRingEnd ℂ) (z x b)).trans (map_zero _))

theorem quot_bcMeas_eq {r' : ℕ} (hS : S.ShortExact) (hS' : S'.ShortExact) (h₁ : IsVB S.X₁ r')
    (h₃ : IsVB S.X₃ s) (h₁' : IsVB S'.X₁ r) (h₃' : IsVB S'.X₃ s) (hT : IsVB T m) (hr : r' = r + m)
    (w : u₁ ≫ S.f = S'.f ≫ u₂) (i₁ : IsIso (biprod.desc u₁ v))
    (i₂ : IsIso (biprod.desc u₂ (v ≫ S.f))) {h : VMetric p S.X₂ (r' + s)}
    {h' : VMetric p S'.X₂ (r + s)} (H : h.IsCInf) (H' : h'.IsCInf)
    (e₁ : ∀ σ (U : X.Opens) (a b : Γ(S'.X₂, U)), ∀ y ∈ ptsIn p σ U,
      (h.met σ).form (u₂.app U a) (u₂.app U b) y = (h'.met σ).form a b y)
    (e₂ : ∀ σ (U : X.Opens) (a : Γ(S'.X₂, U)) (t : Γ(T, U)), ∀ y ∈ ptsIn p σ U,
      (h.met σ).form (u₂.app U a) ((v ≫ S.f).app U t) y = 0) :
    (∃ φ : S'.X₃ ≅ S.X₃, (h'.quot hS' h₁' h₃').IsIsometry (h.quot hS h₁ h₃) φ) ∧
      ∀ σ, (h.met σ).bcMeas hS h₁ h₃ = (h'.met σ).bcMeas hS' h₁' h₃' := by
  subst hr
  obtain ⟨φ, hφ⟩ := exists_iso_X₃ (v := v) hS hS' w
  refine ⟨⟨φ, (isIsometry_iff _).2 (VMetric.ext (funext fun σ => Met.ext_of_exists fun y => ?_))⟩,
    fun σ => ?_⟩
  · obtain ⟨a, f, hf, hy⟩ := exists_adapted_frame hS' h₁' h₃' hT y
    obtain ⟨g₁, g₂, g₃⟩ := gram_sumChart hS w φ hφ (e₁ σ) (e₂ σ) a f hf hy
    have e : (sumChart (u₁ := u₁) (v := v) φ hφ a f hf).quot = a.quot.map φ := by
      have : (fun j => S.g.app a.U (u₂.app a.U (a.t j))) =
          fun j => φ.hom.app a.U (S'.g.app a.U (a.t j)) :=
        funext fun j => congr(($hφ).app a.U (a.t j)).symm
      exact congr(Chart.mk a.U $this _)
    refine ⟨a.quot.map φ, hy, Eq.trans ?_ (((h'.met σ).quot hS' h₁' h₃').map_G φ a.quot hy).symm⟩
    rw [← e, (h'.met σ).quot_G hS' h₁' h₃' a hy]
    exact ((h.met σ).quot_G hS h₁ h₃ _ hy).trans
      ((GlobalTheory.T.submatrix_schur_complement_compat ℂ _ _ _ _ finSumFinEquiv).1 _ _ g₁ g₂ g₃)
  · refine iSup_congr fun c => MeasureTheory.Measure.ext fun A hA => ?_
    rw [ChartGlue.chartMeas_apply _ _ hA, ChartGlue.chartMeas_apply _ _ hA]
    refine MeasureTheory.setLIntegral_congr_fun (ChartGlue.measurableSet_image _
      (c.e.open_source.measurableSet.inter hA) Set.inter_subset_left) ?_
    rintro _ ⟨y, ⟨hc, -⟩, rfl⟩
    obtain ⟨a, f, hf, hy⟩ := exists_adapted_frame hS' h₁' h₃' hT y
    simp only [c.e.left_inv hc]
    rw [Met.bcDens_eq hS h₁ h₃ (sumChart (u₁ := u₁) (v := v) φ hφ a f hf) c (H σ) hc hy,
      Met.bcDens_eq hS' h₁' h₃' a c (H' σ) hc hy, Met.bcForm, Met.bcForm,
      (GlobalTheory.T.submatrix_schur_complement_compat _ _ _ _ _ finSumFinEquiv).2 _ (fun v => (h'.met σ).gram a.frame (c.e.symm v)) _ ?_]
    exact eventually_of_mem ((ChartGlue.isOpen_over c.e (isOpen_ptsIn a.U)).mem_nhds
      (ChartGlue.mem_over c.e hc hy)) fun _ hv => gram_sumChart hS w φ hφ (e₁ σ) (e₂ σ) a f hf hv.2

end Seq

theorem step_eq {E E' E'' T : X.Modules} {N N' m : ℕ} {g : VMetric p E N} {g' : VMetric p E' N'}
    (G : g.IsCInf) (G' : g'.IsCInf) (w : E' ⟶ E) (w' : E'' ⟶ E)
    (hw : ∀ σ (U : X.Opens) (a b : Γ(E', U)), ∀ y ∈ ptsIn p σ U,
      (g.met σ).form (w.app U a) (w.app U b) y = (g'.met σ).form a b y)
    (hw' : ∀ σ (U : X.Opens) (a : Γ(E', U)) (t : Γ(E'', U)), ∀ y ∈ ptsIn p σ U,
      (g.met σ).form (w.app U a) (w'.app U t) y = 0)
    (fl : Vert.Flag E N) (fl' : Vert.Flag E' N') (i : Fin N) (j : Fin N') (hT : IsVB T m)
    (hm : (i : ℕ) = j + m) (u₁ : fl'.F j.castSucc ⟶ fl.F i.castSucc) (u₂ : fl'.F j.succ ⟶ fl.F i.succ)
    (v : T ⟶ fl.F i.castSucc) (τ : T ⟶ E'') (e₁ : u₁ ≫ fl.ι _ = fl'.ι _ ≫ w)
    (e₂ : u₂ ≫ fl.ι _ = fl'.ι _ ≫ w) (e₃ : v ≫ fl.ι _ = τ ≫ w') (i₁ : IsIso (biprod.desc u₁ v))
    (i₂ : IsIso (biprod.desc u₂ (v ≫ fl.step i))) :
    (grLB fl' j G').Isometric (grLB fl i G) ∧ ∀ σ,
      ((g.stepMet fl i).met σ).bcMeas (stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i) =
      ((g'.stepMet fl' j).met σ).bcMeas (stepSeq_shortExact fl' j) (fl'.isVB j.castSucc)
        (fl'.isVB_gr j) := by
  have e₄ : (v ≫ fl.step i) ≫ fl.ι _ = τ ≫ w' := by rw [Category.assoc, fl.step_ι, e₃]
  obtain ⟨⟨φ, hφ⟩, hb⟩ := quot_bcMeas_eq (S := stepSeq fl i) (S' := stepSeq fl' j) (u₁ := u₁)
    (u₂ := u₂) (v := v)
    (stepSeq_shortExact fl i) (stepSeq_shortExact fl' j) (fl.isVB i.castSucc) (fl.isVB_gr i)
    (fl'.isVB j.castSucc) (fl'.isVB_gr j) hT hm
    ((cancel_mono (fl.ι i.succ)).1 (by
      change (u₁ ≫ fl.step i) ≫ _ = (fl'.step j ≫ u₂) ≫ _
      rw [Category.assoc, Category.assoc, fl.step_ι, e₁, e₂, fl'.step_ι_assoc])) i₁ i₂
    (h := g.stepMet fl i) (h' := g'.stepMet fl' j) (G.restrict _ _) (G'.restrict _ _)
    (fun σ U a b y hy => by
      refine (Met.form_restrict (g.met σ) (fl.isSubbundle i.succ) (fl.isVB i.succ) _ _ hy).trans
        (Eq.trans ?_ (Met.form_restrict (g'.met σ) (fl'.isSubbundle j.succ) (fl'.isVB j.succ) _ _
          hy).symm)
      exact (congrArg₂ (fun s t => (g.met σ).form s t y) congr(($e₂).app U a)
        congr(($e₂).app U b)).trans (hw σ U _ _ y hy))
    (fun σ U a t y hy => by
      refine (Met.form_restrict (g.met σ) (fl.isSubbundle i.succ) (fl.isVB i.succ) _ _ hy).trans ?_
      exact (congrArg₂ (fun s t => (g.met σ).form s t y) congr(($e₂).app U a)
        congr(($e₄).app U t)).trans (hw' σ U _ _ y hy))
  exact ⟨GlobalTheory.T.determinant_metric_isometric k X p _ _ 1 _ _ φ _ _ hφ, hb⟩

section Sum

variable {E₁ E₂ : X.Modules} {r s : ℕ} (g₁ : VMetric p E₁ r) (g₂ : VMetric p E₂ s)

theorem form_orthSum_app {A B : X.Modules} (α : A ⟶ E₁ ⊞ E₂) (β : B ⟶ E₁ ⊞ E₂) (σ : k →+* ℂ)
    (U : X.Opens) (a : Γ(A, U)) (b : Γ(B, U)) (y : CxPts p σ) (hy : y ∈ ptsIn p σ U) :
    ((g₁.orthSum g₂).met σ).form (α.app U a) (β.app U b) y =
      (g₁.met σ).form ((α ≫ biprod.fst).app U a) ((β ≫ biprod.fst).app U b) y +
      (g₂.met σ).form ((α ≫ biprod.snd).app U a) ((β ≫ biprod.snd).app U b) y :=
  isOrthSum_orthSum g₁ g₂ σ U _ _ y hy

theorem isIso_incl {E : X.Modules} {N : ℕ} (fl : Vert.Flag E N) {a b : Fin (N + 1)} (h)
    (e : (b : ℕ) = a) : IsIso (fl.incl a b h) := by
  rw [Vert.Flag.incl, dif_pos e]
  infer_instance

theorem isIso_desc {A B C D : X.Modules} (f : A ⟶ C) (g : B ⟶ D) [IsIso f] [IsIso g] :
    IsIso (biprod.desc (f ≫ biprod.inl) (g ≫ biprod.inr)) ∧
      IsIso (biprod.desc (g ≫ (biprod.inr : D ⟶ C ⊞ D)) (f ≫ biprod.inl)) := by
  have e : biprod.desc (f ≫ biprod.inl) (g ≫ biprod.inr) = (biprod.mapIso (asIso f) (asIso g)).hom := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> simp
  have e' : biprod.desc (g ≫ (biprod.inr : D ⟶ C ⊞ D)) (f ≫ biprod.inl) =
      (biprod.braiding B A).hom ≫ (biprod.mapIso (asIso f) (asIso g)).hom := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> refine biprod.hom_ext _ _ ?_ ?_ <;> simp
  rw [e, e']
  exact ⟨inferInstance, inferInstance⟩

variable {g₁ g₂} (G₁ : g₁.IsCInf) (G₂ : g₂.IsCInf) (fl₁ : Vert.Flag E₁ r) (fl₂ : Vert.Flag E₂ s)

theorem step_castAdd (j : Fin r) :
    (grLB fl₁ j G₁).Isometric (grLB (fl₁.biprod fl₂) (j.castAdd s) (G₁.orthSum G₂)) ∧ ∀ σ,
      (((g₁.orthSum g₂).stepMet (fl₁.biprod fl₂) (j.castAdd s)).met σ).bcMeas
        (stepSeq_shortExact (fl₁.biprod fl₂) (j.castAdd s))
        ((fl₁.biprod fl₂).isVB (j.castAdd s).castSucc) ((fl₁.biprod fl₂).isVB_gr (j.castAdd s)) =
      ((g₁.stepMet fl₁ j).met σ).bcMeas (stepSeq_shortExact fl₁ j) (fl₁.isVB j.castSucc)
        (fl₁.isVB_gr j) := by
  have a₁ : j.castSucc = Vert.Flag.fstIdx r s (j.castAdd s).castSucc :=
    Fin.ext (by simp [Vert.Flag.fstIdx])
  have a₂ : j.succ = Vert.Flag.fstIdx r s (j.castAdd s).succ :=
    Fin.ext (by simp [Vert.Flag.fstIdx])
  have := isIso_incl fl₂ (Vert.Flag.sndIdx_step (j.castAdd s))
    (by simp [Vert.Flag.sndIdx])
  refine step_eq (G₁.orthSum G₂) G₁ biprod.inl biprod.inr (fun σ U a b y hy => ?_)
    (fun σ U a b y hy => ?_) _ _ _ _ (fl₂.isVB (Vert.Flag.sndIdx r s (j.castAdd s).castSucc))
    (by simp [Vert.Flag.sndIdx])
    (eqToHom (congrArg fl₁.F a₁) ≫ biprod.inl) (eqToHom (congrArg fl₁.F a₂) ≫ biprod.inl)
    (𝟙 _ ≫ biprod.inr) (fl₂.ι _) ?_ ?_ ?_ (isIso_desc _ _).1 ?_
  · rw [form_orthSum_app _ _ _ _ _ _ _ _ _ hy, biprod.inl_fst, biprod.inl_snd]
    exact (congrArg (_ + ·) (form_zero_left _ _ _)).trans (add_zero _)
  · rw [form_orthSum_app _ _ _ _ _ _ _ _ _ hy, biprod.inl_snd, biprod.inr_fst]
    exact (congrArg₂ (· + ·) (form_zero_right _ _ _) (form_zero_left _ _ _)).trans (add_zero _)
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (biprod.inl_map _ _)).trans
      (fl₁.eqToHom_ι_assoc a₁ _))
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (biprod.inl_map _ _)).trans
      (fl₁.eqToHom_ι_assoc a₂ _))
  · exact (Category.assoc _ _ _).trans ((Category.id_comp _).trans (biprod.inr_map _ _))
  · have e : (𝟙 _ ≫ biprod.inr) ≫ (fl₁.biprod fl₂).step (j.castAdd s) =
        fl₂.incl _ _ (Vert.Flag.sndIdx_step (j.castAdd s)) ≫ biprod.inr :=
      (Category.assoc _ _ _).trans ((Category.id_comp _).trans (biprod.inr_map _ _))
    exact e ▸ (isIso_desc _ _).1

theorem step_natAdd (j : Fin s) :
    (grLB fl₂ j G₂).Isometric (grLB (fl₁.biprod fl₂) (j.natAdd r) (G₁.orthSum G₂)) ∧ ∀ σ,
      (((g₁.orthSum g₂).stepMet (fl₁.biprod fl₂) (j.natAdd r)).met σ).bcMeas
        (stepSeq_shortExact (fl₁.biprod fl₂) (j.natAdd r))
        ((fl₁.biprod fl₂).isVB (j.natAdd r).castSucc) ((fl₁.biprod fl₂).isVB_gr (j.natAdd r)) =
      ((g₂.stepMet fl₂ j).met σ).bcMeas (stepSeq_shortExact fl₂ j) (fl₂.isVB j.castSucc)
        (fl₂.isVB_gr j) := by
  have a₁ : j.castSucc = Vert.Flag.sndIdx r s (j.natAdd r).castSucc :=
    Fin.ext (by simp [Vert.Flag.sndIdx])
  have a₂ : j.succ = Vert.Flag.sndIdx r s (j.natAdd r).succ :=
    Fin.ext (by simp [Vert.Flag.sndIdx]; omega)
  have := isIso_incl fl₁ (Vert.Flag.fstIdx_step (j.natAdd r))
    (by simp [Vert.Flag.fstIdx]; omega)
  refine step_eq (G₁.orthSum G₂) G₂ biprod.inr biprod.inl (fun σ U a b y hy => ?_)
    (fun σ U a b y hy => ?_) _ _ _ _ (fl₁.isVB (Vert.Flag.fstIdx r s (j.natAdd r).castSucc))
    (by simp [Vert.Flag.fstIdx]; omega)
    (eqToHom (congrArg fl₂.F a₁) ≫ biprod.inr) (eqToHom (congrArg fl₂.F a₂) ≫ biprod.inr)
    (𝟙 _ ≫ biprod.inl) (fl₁.ι _) ?_ ?_ ?_ (isIso_desc _ _).2 ?_
  · rw [form_orthSum_app _ _ _ _ _ _ _ _ _ hy, biprod.inr_fst, biprod.inr_snd]
    exact (congrArg (· + _) (form_zero_left _ _ _)).trans (zero_add _)
  · rw [form_orthSum_app _ _ _ _ _ _ _ _ _ hy, biprod.inl_snd, biprod.inr_fst]
    exact (congrArg₂ (· + ·) (form_zero_left _ _ _) (form_zero_right _ _ _)).trans (add_zero _)
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (biprod.inr_map _ _)).trans
      (fl₂.eqToHom_ι_assoc a₁ _))
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (biprod.inr_map _ _)).trans
      (fl₂.eqToHom_ι_assoc a₂ _))
  · exact (Category.assoc _ _ _).trans ((Category.id_comp _).trans (biprod.inl_map _ _))
  · have e : (𝟙 _ ≫ biprod.inl) ≫ (fl₁.biprod fl₂).step (j.natAdd r) =
        fl₁.incl _ _ (Vert.Flag.fstIdx_step (j.natAdd r)) ≫ biprod.inl :=
      (Category.assoc _ _ _).trans ((Category.id_comp _).trans (biprod.inl_map _ _))
    exact e ▸ (isIso_desc _ _).2

theorem isFlagCh2_biprod (HC : Published.ArIso) [IsIntegral X] (hX : IsArithVar p 1) {x y : ℝ}
    (hx : IsFlagCh2 G₁ fl₁ x) (hy : IsFlagCh2 G₂ fl₂ y) :
    IsFlagCh2 (G₁.orthSum G₂) (fl₁.biprod fl₂) (x + y) := by
  obtain ⟨f₁, x, hx, rfl⟩ := hx
  obtain ⟨f₂, y, hy, rfl⟩ := hy
  refine ⟨fun i => ?_, Fin.addCases x y, fun i => ?_, ?_⟩
  · induction i using Fin.addCases with
    | left j => exact fun σ => ((step_castAdd G₁ G₂ fl₁ fl₂ j).2 σ).symm ▸ f₁ j σ
    | right j => exact fun σ => ((step_natAdd G₁ G₂ fl₁ fl₂ j).2 σ).symm ▸ f₂ j σ
  · induction i using Fin.addCases with
    | left j =>
      obtain ⟨h, hh, e⟩ := hx j
      exact ⟨h, (HC k X p 1 hX).1 _ _ h (step_castAdd G₁ G₂ fl₁ fl₂ j).1 hh, by simpa using e⟩
    | right j =>
      obtain ⟨h, hh, e⟩ := hy j
      exact ⟨h, (HC k X p 1 hX).1 _ _ h (step_natAdd G₁ G₂ fl₁ fl₂ j).1 hh, by simpa using e⟩
  · have e : (g₁.orthSum g₂).flagBc (fl₁.biprod fl₂) = g₁.flagBc fl₁ + g₂.flagBc fl₂ := by
      rw [flagBc, Fin.sum_univ_add]
      exact congrArg₂ (· + ·)
        (Finset.sum_congr rfl fun j _ => finsum_congr fun σ =>
          congrArg (fun μ : MeasureTheory.Measure _ => (μ Set.univ).toReal)
            ((step_castAdd G₁ G₂ fl₁ fl₂ j).2 σ))
        (Finset.sum_congr rfl fun j _ => finsum_congr fun σ =>
          congrArg (fun μ : MeasureTheory.Measure _ => (μ Set.univ).toReal)
            ((step_natAdd G₁ G₂ fl₁ fl₂ j).2 σ))
    rw [e, Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right]
    ring

end Sum

noncomputable def compCover [IsIntegral X] (C : RegCover p) (D : RegCover (C.ρ ≫ p)) : RegCover p where
  Y := D.Y
  ρ := D.ρ ≫ C.ρ
  reg := (Category.assoc D.ρ C.ρ p).symm ▸ D.reg
  generic := by
    rw [Scheme.Hom.comp_apply]
    exact (congrArg C.ρ D.generic).trans C.generic
  finite := by
    rw [CurveDegreesCompare.residueDegree_comp]
    exact mul_ne_zero ((congrArg C.ρ.residueDegree D.generic).trans_ne C.finite) D.finite

end GlobalTheory.SecondChernDegreeSum

open GlobalTheory.SecondChernDegreeSum in

theorem GlobalTheory.SecondChernDegreeSum.isCh2Deg_orthSum_of_exists (hex : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X], (∀ (Y : Scheme.{0}) (q : Y ⟶ Sp k) [IsIntegral Y], IsArithVar q 1 → Nonempty (RegCover q)) → IsArithVar p 1 → ∀ (E : X.Modules) (r : ℕ) (h : VMetric p E r), h.IsCInfNorm → ∃ a, h.IsCh2Deg a) : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X], (∀ (Y : Scheme.{0}) (q : Y ⟶ Sp k) [IsIntegral Y], IsArithVar q 1 → Nonempty (RegCover q)) → IsArithVar p 1 → ∀ (E₁ E₂ : X.Modules) (r s : ℕ) (h₁ : VMetric p E₁ r) (h₂ : VMetric p E₂ s) (a b : ℝ), h₁.IsCInfNorm → h₂.IsCInfNorm → h₁.IsCh2Deg a → h₂.IsCh2Deg b → (h₁.orthSum h₂).IsCh2Deg (a + b) := by
  intro HC k _ X p _ hreg hX E₁ E₂ r s h₁ h₂ a b H₁ H₂ ha hb
  have HS : (h₁.orthSum h₂).IsCInfNorm := fun Y π hπ => by
    obtain ⟨φ, hφ⟩ := GlobalTheory.T.orthogonal_sum_pullback_isometric k X Y p _ E₁ E₂ r s h₁ h₂ π rfl
    rw [(VMetric.isIsometry_iff _).1 hφ]
    exact ((H₁ Y π hπ).orthSum (H₂ Y π hπ)).map φ
  obtain ⟨c, hc⟩ := hex HC k X p hreg hX _ _ _ HS
  obtain ⟨M⟩ := ha.1
  obtain ⟨_, ⟨M'⟩, -⟩ := hex HC k M.Y (M.ρ ≫ p) hreg M.reg.toIsArithVar _ _ _
    (VMetric.pull_regCover_isCInf k X p E₂ s h₂ H₂ M.toRegCover).isCInfNorm
  let C := compCover M.toRegCover M'.toRegCover
  let M₁ : h₁.FlagModel := ⟨C, VMetric.pull_regCover_isCInf k X p E₁ r h₁ H₁ C,
    (M.flag.pull M'.ρ).ofIso ((Scheme.Modules.pullbackComp M'.ρ M.ρ).app E₁)⟩
  let M₂ : h₂.FlagModel := ⟨C, VMetric.pull_regCover_isCInf k X p E₂ s h₂ H₂ C,
    M'.flag.ofIso ((Scheme.Modules.pullbackComp M'.ρ M.ρ).app E₂)⟩
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.orthogonal_sum_pullback_isometric k X C.Y p _ E₁ E₂ r s h₁ h₂ C.ρ rfl
  let M₃ : (h₁.orthSum h₂).FlagModel := ⟨C, VMetric.pull_regCover_isCInf k X p _ _ _ HS C,
    (M₁.flag.biprod M₂.flag).ofIso φ⟩
  have h₃ : VMetric.IsFlagCh2 M₃.cInf M₃.flag (C.deg * a + C.deg * b) :=
    (VMetric.isFlagCh2_ofIso k C.Y _ _ _ _ _ _ φ (M₁.cInf.orthSum M₂.cInf) M₃.cInf _ _ hφ).1
      (isFlagCh2_biprod M₁.cInf M₂.cInf M₁.flag M₂.flag HC.arIso C.reg.toIsArithVar (ha.2 M₁)
        (hb.2 M₂))
  have e : c = a + b := by
    rw [hc.eq_div M₃ h₃, ← mul_add]
    exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 C.deg_pos.ne')
  exact e ▸ hc
