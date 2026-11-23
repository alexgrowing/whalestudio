import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.SymmetricPatternGroup

open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.SymCompare
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

section Plain
variable {k : Type*} [Field k] {n m n' m' : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] {c : ℕ}

abbrev sE {n m : Type*} (e : n ≃ m) (c : ℕ) : n ⊕ Fin c ≃ m ⊕ Fin c := e.sumCongr (Equiv.refl _)

theorem reGL_embX (e : n ≃ m) (g : GL n k) : reGL (sE e c) (embX c g) = embX c (reGL e g) := by
  ext (i | i) (j | j) <;> rfl

theorem reGL_embA (e : n ≃ m) (g : GL (Fin c) k) : reGL (sE e c) (embA n g) = embA m g := by
  ext (i | i) (j | j)
  · change (1 : Matrix n n k) (e.symm i) (e.symm j) = (1 : Matrix m m k) i j
    simp [Matrix.one_apply]
  all_goals rfl

theorem reGL_mem_N (e : n ≃ m) {p : ℕ} {g : GL (n ⊕ Fin c) k} : reGL (sE e c) g ∈ N k m c p ↔ g ∈ N k n c p := by
  have hl : ∀ r, lev p (sE e c r) = lev p r := by rintro (r | r) <;> rfl
  rw [Model.mem_N_iff, Model.mem_N_iff]
  constructor
  · intro h r s hrs
    have := h (sE e c r) (sE e c s) (by rwa [hl, hl])
    simpa only [reGL_val, submatrix_apply, Equiv.symm_apply_apply, Matrix.one_apply,
      EmbeddingLike.apply_eq_iff_eq] using this
  · intro h r s hrs
    obtain ⟨r, rfl⟩ := (sE e c).surjective r
    obtain ⟨s, rfl⟩ := (sE e c).surjective s
    have := h r s (by rwa [hl, hl] at hrs)
    simpa only [reGL_val, submatrix_apply, Equiv.symm_apply_apply, Matrix.one_apply,
      EmbeddingLike.apply_eq_iff_eq] using this

theorem reGL_mem_R (e : n ≃ m) {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : g ∈ R k n c p) :
    reGL (sE e c) g ∈ R k m c p := by
  have : R k n c p ≤ (R k m c p).comap (reGL (sE e c)).toMonoidHom := by
    refine sup_le ?_ fun u hu => (le_sup_right : N k m c p ≤ R k m c p) ((reGL_mem_N e).2 hu)
    rintro _ ⟨γ, rfl⟩
    exact (le_sup_left : (embX c).range ≤ R k m c p) ⟨reGL e γ, (reGL_embX e γ).symm⟩
  exact this hg

theorem mul_embX_mem_R {p : ℕ} {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c p) (g : GL n k) :
    u * embX c g ∈ R k n c p :=
  mul_mem ((le_sup_right : N k n c p ≤ R k n c p) hu) ((le_sup_left : (embX c).range ≤ R k n c p) ⟨g, rfl⟩)

theorem prX_inf_eq_iff (J : Subgroup (GL (n ⊕ Fin c) k)) : prX (R k n c 1 ⊓ J) = J.comap (embX c) ↔
    ∀ u ∈ N k n c 1, ∀ g, u * embX c g ∈ J → embX c g ∈ J := by
  constructor
  · intro h u hu g hg
    have : g ∈ prX (R k n c 1 ⊓ J) := ⟨u, hu, mul_embX_mem_R hu g, hg⟩
    rwa [h] at this
  · intro h
    ext g
    exact ⟨fun ⟨u, hu, H⟩ => h u hu g H.2, fun H => ⟨1, one_mem _, mul_embX_mem_R (one_mem _) g, by
      rw [one_mul]; exact H⟩⟩

theorem Cgrp_one (J : Subgroup (GL (n ⊕ Fin c) k)) : Cgrp J 1 = R k n c 1 ⊓ J := by
  ext x; simp [mem_Cgrp]

theorem reGL_conj {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (F : LatFrame k ι n) (F' : LatFrame k ι' m) (a : ι ≃ ι') (b : n ≃ m) (ho : a.trans F'.ord = F.ord.trans b)
    (hb : F'.bas = reGL b F.bas) (g : GL ι k) : F'.conj (reGL a g) = reGL b (F.conj g) := by
  have : reGL F'.ord (reGL a g) = reGL b (reGL F.ord g) := by
    change reGL (a.trans F'.ord) g = reGL (F.ord.trans b) g
    rw [ho]
  rw [LatFrame.conj_apply, LatFrame.conj_apply, this, hb, map_mul, map_mul, map_inv]

theorem coords_submatrix {ι ι' κ κ' : Type*}
    (F : LatFrame k ι n) (F' : LatFrame k ι' m) (a : ι ≃ ι') (b : n ≃ m) (ho : a.trans F'.ord = F.ord.trans b)
    (hb : F'.bas = reGL b F.bas)
    (G : LatFrame k κ n') (G' : LatFrame k κ' m') (a' : κ ≃ κ') (b' : n' ≃ m') (ho' : a'.trans G'.ord = G.ord.trans b')
    (hb' : G'.bas = reGL b' G.bas) (x : Matrix m m' k) :
    (F'.coords G' x).submatrix a a' = F.coords G (x.submatrix b b') := by
  have e1 : (F.bas⁻¹).val = (F'.bas⁻¹).val.submatrix b b := by
    rw [hb, ← map_inv, reGL_val]; simp
  have e2 : G.bas.val = G'.bas.val.submatrix b' b' := by
    rw [hb', reGL_val]; simp
  unfold LatFrame.coords
  rw [e1, e2, submatrix_mul_equiv, submatrix_mul_equiv, submatrix_submatrix, submatrix_submatrix]
  exact congrArg₂ _ (congrArg (fun e : ι ≃ m => (e : ι → m)) ho) (congrArg (fun e : κ ≃ m' => (e : κ → m')) ho')

end Plain

section Local
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n m n' m' : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] {c : ℕ}

theorem om_submatrix (μ : kˣ →* ℂˣ) (E : n ≃ m) (E' : n' ≃ m') (h : GL n k) (Φ : Matrix n n' k → ℂ) :
    om μ 1 (reGL E h) (fun x => Φ (x.submatrix E E')) = fun x => om μ 1 h Φ (x.submatrix E E') := by
  funext x
  simp only [om, det_reGL, ← Fintype.card_congr E, ← Fintype.card_congr E', ← map_inv (reGL _), reGL_val, map_one,
    Units.val_one, Matrix.mul_one]
  congr 2
  rw [← submatrix_mul_equiv _ _ _ E]
  simp

omit [DecidableEq n] [DecidableEq m] [DecidableEq n'] [DecidableEq m'] in
theorem opE_submatrix [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]
    (p : ℕ) (e : n ≃ m) (e' : n' ≃ m') (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix m m' k) :
    opE ψ ν p (fun x => Φ (x.submatrix (sE e c) (sE e' (c + 1)))) x₀ = opE ψ ν p Φ (x₀.submatrix e e') := by
  classical
  have := secondCountable k
  have := t2Space k
  have hf : ∀ r s, Free p (r, s) ↔ Free p (sE e c r, sE e' (c + 1) s) := by
    rintro (r | r) (s | s) <;> exact Iff.rfl
  let σ : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} ≃ {rs : (m ⊕ Fin c) × (m' ⊕ Fin (c + 1)) // Free p rs} :=
    ((sE e c).prodCongr (sE e' (c + 1))).subtypeEquiv fun rs => hf rs.1 rs.2
  have h1 : ∀ f, (affPt p x₀ f).submatrix (sE e c) (sE e' (c + 1)) =
      affPt p (x₀.submatrix e e') (MeasurableEquiv.piCongrLeft (fun _ => k) σ.symm f) := fun f => by
    have h2 : ∀ a, MeasurableEquiv.piCongrLeft (fun _ => k) σ.symm f a = f (σ a) := fun a => by
      obtain ⟨a, rfl⟩ := σ.symm.surjective a
      rw [MeasurableEquiv.piCongrLeft_apply_apply, Equiv.apply_symm_apply]
    ext r s
    have hb : basePt c x₀ (sE e c r) (sE e' (c + 1) s) = basePt c (x₀.submatrix e e') r s := by
      rcases r with r | r <;> rcases s with s | s <;> rfl
    simp only [affPt, submatrix_apply, Matrix.add_apply, hb, of_apply, h2]
    by_cases h : Free p (r, s)
    · rw [dif_pos h, dif_pos ((hf r s).1 h)]; rfl
    · rw [dif_neg h, dif_neg fun H => h ((hf r s).2 H)]
  unfold opE
  rw [← (measurePreserving_piCongrLeft (fun _ => ν) σ.symm).integral_comp']
  simp only [← h1]
  rfl

theorem td_ext {P Q : TypeDatum k n} (hJ : ∀ g, g ∈ P.J ↔ g ∈ Q.J)
    (hl : ∀ g (h : g ∈ P.J) (h' : g ∈ Q.J), P.lam ⟨g, h⟩ = Q.lam ⟨g, h'⟩) : P = Q := by
  obtain ⟨⟨J, l⟩, _, _, _⟩ := P
  obtain ⟨⟨J', l'⟩, _, _, _⟩ := Q
  obtain rfl : J = J' := Subgroup.ext hJ
  obtain rfl : l = l' := MonoidHom.ext fun g => hl g.1 g.2 g.2
  rfl

theorem reindex_trans (P : TypeDatum k n) (e : n ≃ m) (e' : m ≃ n') :
    (P.reindex e).reindex e' = P.reindex (e.trans e') :=
  td_ext (fun _ => Iff.rfl) fun _ _ _ => rfl

theorem reGL_symm_mem_KO (e : n ≃ m) {g : GL m k} : (reGL e).symm g ∈ KO k n ↔ g ∈ KO k m :=
  ⟨fun h => ((TypeDatum.full k n).reindex e).le_KO h, fun h => ((TypeDatum.full k m).reindex e.symm).le_KO
    (show (reGL e.symm).symm ((reGL e).symm g) ∈ KO k m by
      have : (reGL e.symm).symm ((reGL e).symm g) = g := by ext i j; simp [reGL_symm_val]
      rwa [this])⟩

theorem exists_reindex_iff (P : TypeDatum k n) (e : n ≃ m) (M : Matrix m m k) :
    (∃ g ∈ (P.reindex e).J, g.val = M) ↔ ∃ g ∈ P.J, g.val = M.submatrix e e := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨_, hg, rfl⟩
  · rintro ⟨g, hg, h⟩
    refine ⟨reGL e g, ?_, by rw [reGL_val, h]; simp⟩
    change (reGL e).symm (reGL e g) ∈ P.J
    rwa [MulEquiv.symm_apply_apply]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] in
theorem maxM_submatrix (e : n ≃ m) (e' : n' ≃ m') (M : Matrix m m' k) : MaxM (M.submatrix e e') ↔ MaxM M :=
  ⟨fun h i j => by simpa using h (e.symm i) (e'.symm j), fun h _ _ => h _ _⟩

theorem det_reGL_symm (e : n ≃ m) (g : GL m k) :
    Matrix.GeneralLinearGroup.det ((reGL e).symm g) = Matrix.GeneralLinearGroup.det g := by
  rw [← det_reGL e, MulEquiv.apply_symm_apply]

theorem step_reindex (P : TypeDatum k n) (e : n ≃ m) (f : n' ≃ m') (μ : kˣ →* ℂˣ) (hμ : IsTame μ) :
    (P.reindex e).step m' μ hμ = (P.step n' μ hμ).reindex (e.sumCongr f) := by
  refine td_ext (fun g => ?_) fun g h h' => ?_
  · change g ∈ (P.reindex e).stepJ m' ↔ (reGL (e.sumCongr f)).symm g ∈ P.stepJ n'
    rw [TypeDatum.mem_stepJ_iff, TypeDatum.mem_stepJ_iff, reGL_symm_mem_KO, exists_reindex_iff,
      ← maxM_submatrix f e]
    rfl
  · have h1 := (P.reindex e).step_lam μ hμ ⟨g, h⟩ _ (TypeDatum.corner_val _ _)
    have h2 := P.step_lam μ hμ ⟨_, h'⟩ ⟨(reGL e).symm ((P.reindex e).corner ⟨g, h⟩), ((P.reindex e).corner ⟨g, h⟩).2⟩
      (by rw [reGL_symm_val, TypeDatum.corner_val]; rfl)
    have h3 := det_reGL_symm (e.sumCongr f) g
    simp only [det_reGL_symm] at h2
    refine h1.trans (Eq.trans ?_ h2.symm)
    exact congrArg₂ (· * ·) rfl (congrArg μ h3.symm)

omit [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] in
theorem Phi_reindex (P : TypeDatum k n) (e : n ≃ m) (f : n' ≃ m') (μ : kˣ →* ℂˣ) (x : Matrix (m ⊕ m') m k) :
    (P.reindex e).Phi m' μ x = P.Phi n' μ (x.submatrix (e.sumCongr f) e) := by
  have hi : (P.reindex e).Phi m' μ x ≠ 0 ↔ P.Phi n' μ (x.submatrix (e.sumCongr f) e) ≠ 0 := by
    rw [TypeDatum.Phi_ne_zero_iff, TypeDatum.Phi_ne_zero_iff, exists_reindex_iff, ← maxM_submatrix f e]
    rfl
  by_cases h : (P.reindex e).Phi m' μ x = 0
  · rw [h, not_not.1 (hi.not.1 (not_not.2 h))]
  · obtain ⟨⟨g, hg, eg⟩, h2⟩ := (TypeDatum.Phi_ne_zero_iff _ _).1 h
    rw [TypeDatum.Phi_of_mem _ μ ⟨g, hg⟩ eg h2, TypeDatum.Phi_of_mem _ μ (x := x.submatrix (e.sumCongr f) e) ⟨(reGL e).symm g, hg⟩
      (by rw [reGL_symm_val, eg]; rfl) ((maxM_submatrix f e _).2 h2), det_reGL_symm]
    rfl

end Local

section Iter
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r t t' : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] [Fintype t'] [DecidableEq t']

abbrev eI (r : Type*) {t t' : Type*} (f : t ≃ t') (j : ℕ) : Ix r t j ≃ Ix r t' j :=
  (Equiv.refl r).sumCongr ((Equiv.refl (Fin j)).prodCongr f)

theorem ixSucc_eI (r : Type*) {t t' : Type*} (f : t ≃ t') (j : ℕ) :
    ((eI r f j).sumCongr f).trans (ixSucc r t' j) = (ixSucc r t j).trans (eI r f (j + 1)) := by
  ext1 x
  rcases x with (x | x) | x <;> rfl

theorem iter_reindex (f : t ≃ t') (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) :
    P.iter t' μ hμ j = (P.iter t μ hμ j).reindex (eI r f j) := by
  induction j with
  | zero =>
    rw [TypeDatum.iter_zero, TypeDatum.iter_zero, reindex_trans]
    rfl
  | succ j ih =>
    rw [TypeDatum.iter_succ, TypeDatum.iter_succ, ih, step_reindex _ _ f, reindex_trans, reindex_trans, ixSucc_eI]

theorem iterPhi_reindex (f : t ≃ t') (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ)
    (x : Matrix (Ix r t' (j + 1)) (Ix r t' j) k) :
    P.iterPhi t' μ hμ j x = P.iterPhi t μ hμ j (x.submatrix (eI r f (j + 1)) (eI r f j)) := by
  unfold TypeDatum.iterPhi
  rw [iter_reindex f, Phi_reindex _ _ f]
  congr 1
  ext ((i | i) | i) l <;> rfl

theorem stdOrd_eI (κ : Type*) {t t' : Type*} (f : t ≃ t') {l : ℕ} (j c : ℕ) (h : j + c = l) :
    (eI (κ ⊕ Fin l) f j).trans (stdOrd κ t' j c h) = (stdOrd κ t j c h).trans (sE (eI (κ ⊕ Fin j) f j) c) := by
  ext1 x
  rcases x with (x | x) | x
  · rfl
  · rcases H : finSumFinEquiv.symm (finCongr (by omega : l = c + j) x) with a | a <;>
      simp [stdOrd, -finCongr_apply, H]
  · rfl

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {s : ℕ}

theorem typeChain_lev (f : t ≃ t') (ϖ : kˣ) (P : TypeDatum k (κ ⊕ Fin (s + 1))) (μ : ℕ → kˣ →* ℂˣ)
    (hμ : ∀ j, IsTame (μ j)) (j c : ℕ) (h : j + c = s + 1) (g : GL (XIx κ t j ⊕ Fin c) k) :
    reGL (sE (eI (κ ⊕ Fin j) f j) c) g ∈ ((typeChain t' ϖ P μ hμ).lev j c h).J ↔
      g ∈ ((typeChain t ϖ P μ hμ).lev j c h).J := by
  obtain ⟨g, rfl⟩ := (typeFrame ϖ (stdOrd κ t j c h)).conj.surjective g
  rw [← reGL_conj (typeFrame ϖ (stdOrd κ t j c h)) (typeFrame ϖ (stdOrd κ t' j c h)) _ _ (stdOrd_eI κ f j c h)
    (reGL_embA _ _).symm]
  change (typeFrame ϖ (stdOrd κ t' j c h)).conj.symm _ ∈ (P.iter t' μ hμ j).J ↔
    (typeFrame ϖ (stdOrd κ t j c h)).conj.symm _ ∈ (P.iter t μ hμ j).J
  rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, iter_reindex f]
  change (reGL (eI _ f j)).symm (reGL (eI _ f j) g) ∈ (P.iter t μ hμ j).J ↔ _
  rw [MulEquiv.symm_apply_apply]

theorem typeChain_Phi (f : t ≃ t') (ϖ : kˣ) (P : TypeDatum k (κ ⊕ Fin (s + 1))) (μ : ℕ → kˣ →* ℂˣ)
    (hμ : ∀ j, IsTame (μ j)) (j c : ℕ) (h : j + c = s) :
    (typeChain t' ϖ P μ hμ).Phi j c h = fun x => (typeChain t ϖ P μ hμ).Phi j c h
      (x.submatrix (sE (eI (κ ⊕ Fin (j + 1)) f (j + 1)) c) (sE (eI (κ ⊕ Fin j) f j) (c + 1))) := by
  funext x
  change P.iterPhi t' μ hμ j _ = P.iterPhi t μ hμ j _
  rw [iterPhi_reindex f]
  exact congrArg _ (coords_submatrix (typeFrame ϖ (stdOrd κ t (j + 1) c (by omega)))
    (typeFrame ϖ (stdOrd κ t' (j + 1) c (by omega))) _ _ (stdOrd_eI κ f (j + 1) c (by omega)) (reGL_embA _ _).symm
    (typeFrame ϖ (stdOrd κ t j (c + 1) (by omega))) (typeFrame ϖ (stdOrd κ t' j (c + 1) (by omega))) _ _
    (stdOrd_eI κ f j (c + 1) (by omega)) (reGL_embA _ _).symm x)

end Iter

end GlobalTheory.SymCompare
