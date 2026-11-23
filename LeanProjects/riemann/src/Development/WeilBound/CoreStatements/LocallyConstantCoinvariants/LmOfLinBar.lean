import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ActsFormula
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsUnitDetOfCartan

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.KCo

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E} {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype κ] {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} {ψ : AddChar (AF F) ℂ}

theorem Grams.swap (hG : Grams σ t JA JB) : Grams σ t JB JA := by
  obtain ⟨ε, h1, h2, h3⟩ := hG.sym
  exact ⟨hG.uB, hG.uA, -ε, by rw [neg_mul_neg, h1], h3, by rw [neg_neg, h2]⟩

theorem bij_comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {ι : (X → ℂ) →ₗ[ℂ] (Y → ℂ)}
    (hb : Set.BijOn ι (SB X : Set _) (SB Y : Set _)) (e : Z ≃ₜ Y) :
    Set.BijOn (LinearMap.funLeft ℂ ℂ e ∘ₗ ι) (SB X : Set _) (SB Z : Set _) := by
  have hb' : Set.BijOn (LinearMap.funLeft ℂ ℂ e) (SB Y : Set _) (SB Z : Set _) := by
    refine ⟨fun Φ h => ?_, fun a _ b _ h => funext fun y => ?_, fun Φ h => ⟨Φ ∘ e.symm, ?_, funext fun z => by simp⟩⟩
    · exact And.intro (h.1.comp_continuous e.continuous) (h.2.comp_homeomorph e)
    · simpa using congrFun h (e.symm y)
    · exact And.intro (h.1.comp_continuous e.symm.continuous) (h.2.comp_homeomorph e.symm)
  exact hb'.comp hb

def swH (k α β : Type) [TopologicalSpace k] : (β × α → k) ≃ₜ (α × β → k) := Homeomorph.piCongrLeft (Y := fun _ => k) (Equiv.prodComm β α)

theorem swH_apply {k α β : Type} [TopologicalSpace k] (y : β × α → k) : swH k α β y = fun p => y p.swap := by
  funext p
  simp [swH, Homeomorph.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft']

def ofH (k α β : Type) [TopologicalSpace k] : Matrix α β k ≃ₜ (α × β → k) where
  toFun := ofM
  invFun := toM
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)
  continuous_invFun := continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)

theorem LM.swap {d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ} {ι} (hι : LM t ψ d ι)
    {d' : Darboux (symp (R := AF F) (cA σ) (-1) JB JA) κ} (hd : ∀ x : Matrix α β (AE F E), d'.e xᵀ = d.e x) :
    LM t ψ d' (LinearMap.funLeft ℂ ℂ (swH (Fv F v) α β) ∘ₗ ι) := by
  refine ⟨bij_comp hι.bij _, fun u φ hφ => funext fun y => ?_⟩
  have e1 : (coord σ t JA JB uᵀ).1 = fun p => (coord σ t JB JA u).1 p.swap := by
    have : JA.map (piW t) * uᵀ.map (piW (t.comp σ)) * (JB.map (piW t))ᵀ =
        (JB.map (piW t) * u.map (piW (t.comp σ)) * (JA.map (piW t))ᵀ)ᵀ := by
      rw [transpose_mul, transpose_mul, transpose_transpose, transpose_map, Matrix.mul_assoc]
    rw [coord, this]; rfl
  have e2 : (coord σ t JA JB uᵀ).2 = fun p => (coord σ t JB JA u).2 p.swap := rfl
  have dt : ∀ a b : β × α → Fv F v, (fun p : α × β => a p.swap) ⬝ᵥ (fun p => b p.swap) = a ⬝ᵥ b := fun a b =>
    (Equiv.prodComm α β).sum_comp fun p => a p * b p
  rw [← transpose_transpose u, hd, transpose_transpose]
  simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, hι.Heisenberg₂ _ φ hφ, schr, swH_apply, e1, e2, dt]
  rfl

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}

theorem incM_map (h : IsSec σ t sec) {a b : Type} (J : Matrix a b E) : (incM F J).map (piW t) = J.map t :=
  Matrix.ext fun i j => by rw [incM, map_apply, map_apply, map_apply]; exact (h.inc (J i j)).1

theorem incM_map' (h : IsSec σ t sec) {a b : Type} (J : Matrix a b E) (i j) :
    (incM F J).map (piW (t.comp σ)) i j = t (σ (J i j)) := by rw [incM, map_apply, map_apply]; exact (h.inc (J i j)).2

theorem co_eq (h : IsSec σ t sec) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map t * u.map (piW (t.comp σ)) * (W.J.map t)ᵀ * (1 : GL (Fin d) (Fv F v)).1) =
      toM (coord σ t (incM F X.J) (incM F W.J) u).1 := by
  rw [coord, incM_map h, incM_map h, toM_ofM, Units.val_one, Units.val_one, transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem coord_snd {u : Matrix α β (AE F E)} : (coord σ t JA JB u).2 = 0 ↔ u.map (piW t) = 0 :=
  ⟨fun h => neg_eq_zero.1 (congrArg toM h), fun h => by rw [coord, h, neg_zero]; rfl⟩

theorem coord_fst {u : Matrix α β (AE F E)} (h : u.map (piW (t.comp σ)) = 0) : (coord σ t JA JB u).1 = 0 := by
  rw [coord, h, Matrix.mul_zero, Matrix.zero_mul, neg_zero]; rfl

theorem linBar_of_lm (hA : AdSt) (hU : ActsUniq) (h : IsSec σ t sec) (hG : Grams σ t (incM F X.J) (incM F W.J)) {ι}
    (hι : LM t ψ M.co ι) : M.IsLinBar ψ t 1 1 (LinearMap.funLeft ℂ ℂ (ofH (Fv F v) (Fin n) (Fin d)) ∘ₗ ι) := by
  have k : ∀ u, At (evFin F v) u → ∀ φ ∈ SB _, ∀ φ₁, Acts (evFin F v) (M.co.rho ψ u) φ φ₁ →
      ι φ₁ = schr (psiV ψ v) (coord σ t (incM F X.J) (incM F W.J) u) (ι φ) := fun u hu φ hφ φ₁ ha => by
    rw [hU F _ v _ φ hφ _ _ ha (hA.Heisenberg₂ F _ ψ v _ (hu.kd_map M.co.e.toLinearMap) φ)]
    exact hι.Heisenberg₂ u φ hφ
  refine ⟨bij_comp hι.bij _, fun u hu h0 φ hφ φ₁ _ ha Y => ?_, fun u hu h0 φ hφ φ₁ _ ha x hx hx0 => ?_⟩
  · simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, k u hu φ hφ φ₁ ha, schr, coord_snd.2 h0, dotProduct_zero, mul_zero,
      add_zero, AddChar.map_zero_eq_one, one_mul, co_eq h]
    rfl
  · simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, k u hu φ hφ φ₁ ha, schr, coord_fst h0, zero_dotProduct, mul_zero,
      add_zero, co_eq h, symp_eq h hG hx, sub_zero]
    rfl

theorem lm_of_linBar (hA : AdSt) (hψ : IsStd ψ) (h : IsSec σ t sec) (hG : Grams σ t (incM F X.J) (incM F W.J)) {ι}
    (hι : M.IsLinBar ψ t 1 1 ι) : LM t ψ M.co (LinearMap.funLeft ℂ ℂ (ofH (Fv F v) (Fin n) (Fin d)).symm ∘ₗ ι) := by
  have hc := ((hA.psi F ψ hψ).2 v).1
  obtain ⟨e, he1, he⟩ := exists_e h hG M.co
  set ι' := LinearMap.funLeft ℂ ℂ (ofH (Fv F v) (Fin n) (Fin d)).symm ∘ₗ ι
  have a1 : ∀ y, ∀ φ ∈ SB _, ι' (schr (psiV ψ v) (e (y, 0)) φ) = schr (psiV ψ v) (y, 0) (ι' φ) := fun y φ hφ => funext fun z => by
    obtain ⟨u, hu, hco, -⟩ := exists_coord h hG (y, 0)
    have := hι.trans u hu (coord_snd.1 (congrArg Prod.snd hco)) φ hφ _ (schr_mem hc _ hφ)
      (hA.Heisenberg₂ F _ ψ v _ (hu.kd_map M.co.e.toLinearMap) φ) (toM z)
    rw [co_eq h, hco] at this
    rw [← hco, he, hco]
    simp only [schr, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul]
    exact this
  have a2 : ∀ y, ∀ φ ∈ SB _, ι' (schr (psiV ψ v) (e (0, y)) φ) = schr (psiV ψ v) (0, y) (ι' φ) := fun y φ hφ => funext fun z => by
    obtain ⟨u, hu, hco, h0⟩ := exists_coord h hG (0, y)
    obtain ⟨x, hx, hcx, -⟩ := exists_coord h hG (z, 0)
    have := hι.mult u hu (h0 rfl) φ hφ _ (schr_mem hc _ hφ) (hA.Heisenberg₂ F _ ψ v _ (hu.kd_map M.co.e.toLinearMap) φ) x hx
      (coord_snd.1 (congrArg Prod.snd hcx))
    rw [co_eq h, symp_eq h hG hx, hco, hcx] at this
    rw [← hco, he, hco]
    simp only [schr, zero_dotProduct, mul_zero, add_zero, sub_zero] at this ⊢
    exact this
  refine ⟨bij_comp hι.bij _, fun u φ hφ => ?_⟩
  rw [← he]
  obtain ⟨y, z⟩ := coord σ t (incM F X.J) (incM F W.J) u
  have b := a1 y _ (schr_mem hc (e (0, z)) hφ)
  rw [a2 z φ hφ, schr_schr, schr_schr, he1, ← map_add, map_smul] at b
  simp only [Prod.mk_add_mk, add_zero, zero_add] at b
  exact smul_right_injective _ (AddChar.val_isUnit _ _).ne_zero b

def DictX : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (B : Base F E)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (om : Rep σ X W) (χX χW : Chr F E), B.IsGood σ → (∃ r s, X.IsHerm σ B r s) →
    (∃ r s, W.IsSkew σ B r s) → M.IsWeil B.ψ χX χW om → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), (∃ ι, M.IsLinBar B.ψ t 1 1 ι) ∧
      (∀ g₀ : GL (Fin n) (Fv F v), ∃ g ∈ UAt σ X (evFin F v), (mat g).map (piW t) = g₀) ∧
      (∀ h₀ : GL (Fin d) (Fv F v), ∃ h ∈ UAt σ W (evFin F v), (mat h).map (piW t) = h₀) ∧
      ∀ ι, M.IsLinBar B.ψ t 1 1 ι →
        (∀ g ∈ UAt σ X (evFin F v), ∀ g₀ : GL (Fin n) (Fv F v), (mat g).map (piW t) = g₀ →
          Reads v ι (om (g, 1)) (omB (chrW χW t) (chrW χX t) g₀ 1)) ∧
        ∀ h ∈ UAt σ W (evFin F v), ∀ h₀ : GL (Fin d) (Fv F v), (mat h).map (piW t) = h₀ →
          Reads v ι (om (1, h)) (omB (chrW χW t) (chrW χX t) 1 h₀)

theorem dictX_of (hM : ModelEx) (hC : Cyc) (hA : AdSt) (hS : SecSt) (hU : ActsUniq) : DictX := by
  intro F E _ _ _ _ _ σ n d B X W M om χX χW hB ⟨_, _, hX⟩ ⟨_, _, hW⟩ hom v t
  obtain ⟨⟨sec, h⟩, -⟩ := hS F E σ hB.cm v t
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have uu : ∀ {m : ℕ} {J : Matrix (Fin m) (Fin m) E}, IsUnit J.det → IsUnit ((incM F J).map (piW t)) := fun {m J} hJ => by
    rw [incM_map h]
    exact ((Matrix.isUnit_iff_isUnit_det J).2 hJ).map (t : E →+* Fv F v).mapMatrix
  have hG : Grams σ t (incM F X.J) (incM F W.J) := by
    refine ⟨uu (GlobalTheory.CompanionTheory.Ar.RT.isUnit_det_of_cartan (F := F) X.J (B.emb w).1 1 (X.θ w) (by rw [one_smul]; exact hX.cartan w)),
      uu (GlobalTheory.CompanionTheory.Ar.RT.isUnit_det_of_cartan (F := F) W.J (B.emb w).1 Complex.I (W.θ w) (hW.cartan w)), 1, one_mul _,
      Matrix.ext fun i j => ?_, Matrix.ext fun i j => ?_⟩
    · rw [incM_map' h, incM_map h, one_smul, hX.herm]; rfl
    · rw [incM_map' h, incM_map h, neg_smul, one_smul, hW.skew, map_neg]; rfl
  obtain ⟨ι₀, hι₀⟩ := exists_lm hM hA hB.std h hG M.co
  obtain ⟨hR, ⟨d', hd', hL⟩, -⟩ := hom
  obtain ⟨ε, -, hε, hε'⟩ := hG.sym
  refine ⟨⟨_, linBar_of_lm hA hU h hG hι₀⟩, fun g₀ => h.exists_ug hε hG.uA g₀, fun g₀ => h.exists_ug hε' hG.uB g₀, fun ι hι => ?_⟩
  have lm := lm_of_linBar hA hB.std h hG hι
  refine ⟨fun g hg g₀ e φ hφ => ?_, fun g hg g₀ e φ hφ => ?_⟩
  · obtain ⟨φ₁, h1, h2, h3⟩ := acts_formula hM hC hA hB.std h hG.swap (lm.swap hd') hL.isWeilB g hg g₀ e φ hφ
    refine ⟨φ₁, h1, h2, funext fun Y => ?_⟩
    have := congrFun h3 (ofM Yᵀ)
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, Pi.smul_apply, rmL_apply, swH_apply, toM_ofM, smul_eq_mul] at this
    simp only [omB, gdet, map_one, Units.val_one, mul_one, apow_one, Matrix.mul_one]
    refine this.trans (congrArg _ (congrArg _ ?_))
    rw [← transpose_transpose (g₀.1ᵀ * Y), transpose_mul, transpose_transpose]
    rfl
  · obtain ⟨φ₁, h1, h2, h3⟩ := acts_formula hM hC hA hB.std h hG lm hR.isWeilB g hg g₀ e φ hφ
    refine ⟨φ₁, h1, h2, funext fun Y => ?_⟩
    have := congrFun h3 (ofM Y)
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, Pi.smul_apply, rmL_apply, toM_ofM, smul_eq_mul] at this
    simp only [omB, gdet, map_one, Units.val_one, mul_one, one_mul, apow_one, transpose_one, Matrix.one_mul]
    exact this

theorem dictSt_of (hX : DictX) (hS : SecSt) : DictSt := by
  intro F E _ _ _ _ _ σ n d B X W M om χX χW hB h1 h2 _ hom hχX hχW v t
  obtain ⟨e, s1, s2, k⟩ := hX F E σ n d B X W M om χX χW hB h1 h2 hom v t
  have hu := (hS F E σ hB.cm v t).2
  refine ⟨e, _, _, hu χW hχW, hu χX hχX, fun _ _ h => Or.inl h, fun ι hι => ⟨fun g hg => ⟨_, (k ι hι).1 g hg
    (GeneralLinearGroup.map (piW t) g.1) rfl⟩, fun g₀ => ?_, fun g hg => ⟨_, (k ι hι).2 g hg (GeneralLinearGroup.map (piW t) g.1) rfl⟩,
      fun g₀ => ?_⟩⟩
  · obtain ⟨g, hg, e⟩ := s1 g₀
    exact ⟨g, hg, (k ι hι).1 g hg g₀ e⟩
  · obtain ⟨g, hg, e⟩ := s2 g₀
    exact ⟨g, hg, (k ι hι).2 g hg g₀ e⟩

end PositivityTheory.KCo
