import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntLocConjIntLocConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open scoped TensorProduct
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdelicU GlobalTheory.TamOne

noncomputable section

namespace GlobalTheory.TamOneGlob

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem latLoc_le_smul_of_ne {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) {u v : HeightOneSpectrum (𝓞 F)}
    (h : u ≠ v) (k : ℕ) :
    latLoc F Λ u ≤ latLoc F (((v.asIdeal ^ k).map (algebraMap (𝓞 F) (𝓞 E))) • Λ) u := by
  obtain ⟨s, hs, hsu⟩ : ∃ s ∈ v.asIdeal ^ k, s ∉ u.asIdeal := by
    by_contra hc
    push_neg at hc
    have hle : v.asIdeal ≤ u.asIdeal := u.isPrime.le_of_pow_le hc
    exact h (HeightOneSpectrum.ext ((v.isMaximal.eq_of_le u.isPrime.ne_top hle).symm))
  set c : F := algebraMap (𝓞 F) F s with hcdef
  have hval : Valued.v (algebraMap F (Fv F u) c) = 1 := by
    rw [show algebraMap F (Fv F u) c = (c : u.adicCompletion F) from rfl, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      hcdef, HeightOneSpectrum.valuation_eq_one_iff_notMem]
    exact hsu
  have hc0 : algebraMap F (Fv F u) c ≠ 0 := fun e => by rw [e, map_zero] at hval; exact zero_ne_one hval
  have hunit : (algebraMap F (Fv F u) c)⁻¹ ∈ u.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval, inv_one]
  intro y hy
  refine latLoc_induction (p := fun y => y ∈ latLoc F _ u) (fun a ha x hx => ?_) (zero_mem _)
    (fun _ _ => add_mem) (fun _ => neg_mem) hy
  have hx' : (algebraMap (𝓞 F) (𝓞 E) s) • x ∈ ((v.asIdeal ^ k).map (algebraMap (𝓞 F) (𝓞 E))) • Λ :=
    Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hs) hx
  convert tmul_mem_latLoc (mul_mem ha hunit) hx' using 1
  funext i
  have e1 : ((algebraMap (𝓞 F) (𝓞 E) s) • x) i = c • x i := by
    simp only [hcdef, Pi.smul_apply, Algebra.smul_def]
    congr 1
  rw [e1, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm a, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]

theorem eq_one_of_comp (z : AF F ⊗[F] E) (hf : ∀ v, compFin F E v z = 1) (hi : ∀ w, compInf F E w z = 1) :
    z = 1 := by
  have h1 : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z = 1 := by
    refine GlobalTheory.AutFunCompare.infTens_ext fun w => ?_
    rw [map_one, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
    exact hi w
  have h2 : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z = 1 := by
    refine GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun v => ?_
    rw [map_one, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
    exact hf v
  have := GlobalTheory.AutFunCounterexample.tens_inj (F := F) (E := E) (A := Ainf F) (B := Af F) (n := 1)
    (Matrix.of fun _ _ => z) (by ext i j; fin_cases i; fin_cases j; exact h1.trans (Matrix.one_apply_eq (0 : Fin 1)).symm)
    (by ext i j; fin_cases i; fin_cases j; exact h2.trans (Matrix.one_apply_eq (0 : Fin 1)).symm)
  have h3 := congrFun (congrFun this 0) 0
  exact h3.trans (Matrix.one_apply_eq (0 : Fin 1))

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem det_proj (v : HeightOneSpectrum (𝓞 F)) (g : GAd σ J) :
    ((matHom _ σ J (proj σ J v g) : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det =
      compFin F E v ((matHom _ σ J g : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).det := by
  rw [matHom_proj, RingHom.map_det]; rfl

theorem det_projArch (w : InfinitePlace F) (g : GAd σ J) :
    ((matHom _ σ J (projArch σ J w g) : GL (Fin n) (w.Completion ⊗[F] E)) : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)).det =
      compInf F E w ((matHom _ σ J g : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).det := by
  rw [matHom_projArch, RingHom.map_det]; rfl

theorem proj_mem_stabOne {Λ : Submodule (𝓞 E) (Fin n → E)} (hΛ : Λ.FG) (v : HeightOneSpectrum (𝓞 F))
    (a : stabSet σ J Λ) : proj σ J v a.1.1 ∈ stabOne σ J Λ v := by
  refine ⟨?_, ?_⟩
  · rw [det_proj]
    have := GlobalTheory.Published.StrongApprox.mem_SUAdelic.1 a.1.2
    rw [matHom_apply, this, map_one]
  · exact (mem_levelOpen.1 ((mem_levelOpen_iff_latHat σ J hΛ a.1.1).2 a.2)) v

theorem emb_mem_SUAdelic (v : HeightOneSpectrum (𝓞 F)) (x : GLoc σ J v)
    (hx : ((matHom _ σ J x : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det = 1) :
    emb σ J v x ∈ GlobalTheory.Published.SUAdelic σ J := by
  rw [GlobalTheory.Published.StrongApprox.mem_SUAdelic, ← matHom_apply]
  refine eq_one_of_comp _ (fun u => ?_) (fun w => ?_)
  · rw [← det_proj]
    by_cases e : u = v
    · subst e; rw [proj_emb_self, hx]
    · rw [proj_emb_ne σ J e]; simp
  · rw [← det_projArch, projArch_emb]; simp

theorem emb_mem_stabSet {Λ : Submodule (𝓞 E) (Fin n → E)} (hΛ : Λ.FG) (v : HeightOneSpectrum (𝓞 F))
    (x : GLoc σ J v) (hx : x ∈ stabOne σ J Λ v) :
    (⟨emb σ J v x, emb_mem_SUAdelic σ J v x hx.1⟩ : GlobalTheory.Published.SUAdelic σ J) ∈ stabSet σ J Λ := by
  refine (mem_levelOpen_iff_latHat σ J hΛ (emb σ J v x)).1 (mem_levelOpen.2 fun u => ?_)
  rcases eq_or_ne u v with rfl | e
  · rw [proj_emb_self]; exact hx.2
  · rw [proj_emb_ne σ J e]; exact one_mem _

theorem rel_iff {Λ : Submodule (𝓞 E) (Fin n → E)} (hΛ : Λ.FG) (v : HeightOneSpectrum (𝓞 F)) (k : ℕ)
    {a b : GAd σ J} (ha : a ∈ levelOpen σ J Λ) (hb : b ∈ levelOpen σ J Λ) :
    (∀ y ∈ latHat F E (Λ : Set (Fin n → E)), (finMat σ J a - finMat σ J b) *ᵥ y ∈
        latHat F E ((((v.asIdeal ^ k).map (algebraMap (𝓞 F) (𝓞 E))) • Λ : Submodule (𝓞 E) (Fin n → E)) :
          Set (Fin n → E))) ↔
      ∀ z ∈ latLoc F Λ v,
        (((matHom _ σ J (proj σ J v a) : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) -
          ((matHom _ σ J (proj σ J v b) : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) *ᵥ z ∈
          latLoc F (((v.asIdeal ^ k).map (algebraMap (𝓞 F) (𝓞 E))) • Λ) v := by
  have hΛ' : (((v.asIdeal ^ k).map (algebraMap (𝓞 F) (𝓞 E))) • Λ).FG := by
    haveI := isNoetherian_of_fg_of_noetherian Λ hΛ
    exact Submodule.FG.of_le_of_isNoetherian Submodule.smul_le_right
  have key : ∀ u y, vecLoc u ((finMat σ J a - finMat σ J b) *ᵥ y) =
      (((matHom _ σ J (proj σ J u a) : GL (Fin n) (Fv F u ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F u ⊗[F] E)) -
        ((matHom _ σ J (proj σ J u b) : GL (Fin n) (Fv F u ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F u ⊗[F] E))) *ᵥ
        vecLoc u y := by
    intro u y
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, ← vecLoc_mulVec, ← vecLoc_mulVec]
    funext i
    exact map_sub _ _ _
  simp only [mem_latHat_iff hΛ, mem_latHat_iff hΛ', key]
  constructor
  · intro h z hz
    let y : Fin n → Af F ⊗[F] E := fun i => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (singleFin v) (singleFin_mul v) (z i)
    have h1 : vecLoc v y = z :=
      funext fun i => GlobalTheory.AutFunCompare.map_tensNU_self _ _ _ (evalV_singleFin_self v) _
    have h2 : ∀ u, u ≠ v → vecLoc u y = 0 := fun u hu =>
      funext fun i => GlobalTheory.AutFunCompare.map_tensNU_zero _ _ _ (evalV_singleFin_ne hu) _
    have := h y (fun u => by
      rcases eq_or_ne u v with rfl | e
      · rw [h1]; exact hz
      · rw [h2 u e]; exact zero_mem _) v
    rwa [h1] at this
  · intro h y hy u
    rcases eq_or_ne u v with rfl | e
    · exact h _ (hy u)
    · refine latLoc_le_smul_of_ne Λ e k ?_
      rw [Matrix.sub_mulVec]
      exact sub_mem ((mem_stabLoc.1 (mem_levelOpen.1 ha u) _).1 (hy u))
        ((mem_stabLoc.1 (mem_levelOpen.1 hb u) _).1 (hy u))

theorem card_quot_eq_of_surj {α β : Type} (r : α → α → Prop) (s : β → β → Prop) (hs : Equivalence s) (f : α → β)
    (hf : Function.Surjective f) (h : ∀ a b, r a b ↔ s (f a) (f b)) : Nat.card (Quot r) = Nat.card (Quot s) := by
  refine Nat.card_congr (Equiv.ofBijective (Quot.map f fun a b hab => (h a b).1 hab) ⟨?_, ?_⟩)
  · intro p q
    induction p using Quot.ind with | mk a => ?_
    induction q using Quot.ind with | mk b => ?_
    intro hpq
    exact Quot.sound ((h a b).2 (hs.eqvGen_iff.1 (Quot.eqvGen_exact hpq)))
  · intro q
    induction q using Quot.ind with | mk x => ?_
    obtain ⟨a, rfl⟩ := hf x
    exact ⟨Quot.mk _ a, rfl⟩

theorem congRel_equiv (Λ : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) (𝔞 : Ideal (𝓞 E)) :
    Equivalence (congRel σ J Λ v 𝔞) where
  refl x z _ := by rw [sub_self, Matrix.zero_mulVec]; exact zero_mem _
  symm {x y} h z hz := by rw [← neg_sub, Matrix.neg_mulVec]; exact neg_mem (h z hz)
  trans {x y w} h1 h2 z hz := by
    have := add_mem (h1 z hz) (h2 z hz)
    rwa [← Matrix.add_mulVec, sub_add_sub_cancel] at this

end GlobalTheory.TamOneGlob

open GlobalTheory.TamOneGlob in

theorem GlobalTheory.TamOne.locCount_eq_card_congRel : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)), Λ.FG → ∀ (v : HeightOneSpectrum (𝓞 F)) (k : ℕ), locCount σ J Λ v k = Nat.card (Quot (congRel σ J Λ v ((v.asIdeal ^ k).map (algebraMap (𝓞 F) (𝓞 E))))) := by
  intro F E _ _ _ _ _ σ n J Λ hΛ v k
  unfold locCount
  have hlev : ∀ a : stabSet σ J Λ, a.1.1 ∈ levelOpen σ J Λ := fun a =>
    (mem_levelOpen_iff_latHat σ J hΛ a.1.1).2 a.2
  refine card_quot_eq_of_surj _ _ (congRel_equiv σ J Λ v _)
    (fun a : stabSet σ J Λ => (⟨proj σ J v a.1.1, proj_mem_stabOne σ J hΛ v a⟩ : stabOne σ J Λ v))
    (fun x => ⟨⟨⟨emb σ J v x.1, emb_mem_SUAdelic σ J v x.1 x.2.1⟩, emb_mem_stabSet σ J hΛ v x.1 x.2⟩,
      Subtype.ext (proj_emb_self σ J v x.1)⟩)
    (fun a b => rel_iff σ J hΛ v k (hlev a) (hlev b))
