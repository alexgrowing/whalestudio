import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PBData
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.PresBC

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MvPolynomial CrystallineSemistableComparison CrystallineSemistableComparison.Onto

namespace UpperTheory.Gal.KunnethLefschetz.G

private theorem stdC (A : Type) [CommRing A] (D : ℕ) :
    (MvPolynomial.C : A →+* MvPolynomial (Fin D) A).IsStandardSmoothOfRelativeDimension D := by
  let P₀ : Algebra.Presentation A (MvPolynomial (Fin D) A) (Fin D) Empty :=
    { __ := Algebra.Generators.mvPolynomial A (Fin D)
      relation := Empty.elim
      span_range_relation_eq_ker := by
        rw [Algebra.Generators.ker_mvPolynomial]
        simp }
  let P₁ : Algebra.PreSubmersivePresentation A (MvPolynomial (Fin D) A) (Fin D) Empty :=
    { __ := P₀
      map := Empty.elim
      map_inj := fun a => a.elim }
  let P₂ : Algebra.SubmersivePresentation A (MvPolynomial (Fin D) A) (Fin D) Empty :=
    { __ := P₁
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
        simp }
  have : Algebra.IsStandardSmoothOfRelativeDimension D A (MvPolynomial (Fin D) A) :=
    P₂.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap D).2 this

private theorem etale_quot {A E R : Type} [CommRing A] [CommRing E] [CommRing R] {D : ℕ}
    (p : A →+* E) (q : E →+* R) (s : Fin D → E) (hφ : (eval₂Hom p s).Etale)
    (surj : Function.Surjective q) (ker : RingHom.ker q = Ideal.span (Set.range s)) :
    (q.comp p).Etale := by
  obtain ⟨φ, hφd⟩ : ∃ φ : MvPolynomial (Fin D) A →+* E, φ = eval₂Hom p s := ⟨_, rfl⟩
  obtain ⟨σ, hσd⟩ : ∃ σ : MvPolynomial (Fin D) A →+* A, σ = eval₂Hom (RingHom.id A) (fun _ => 0) := ⟨_, rfl⟩
  rw [← hφd] at hφ
  have φC : ∀ x, φ (MvPolynomial.C x) = p x := fun x => by rw [hφd, eval₂Hom_C]
  have φX : ∀ k, φ (X k) = s k := fun k => by rw [hφd, eval₂Hom_X']
  have σC : ∀ x, σ (MvPolynomial.C x) = x := fun x => by rw [hσd, eval₂Hom_C]; rfl
  have σX : ∀ k, σ (X k) = 0 := fun k => by rw [hσd, eval₂Hom_X']
  have qs : ∀ k, q (s k) = 0 := fun k => by
    have : s k ∈ RingHom.ker q := by rw [ker]; exact Ideal.subset_span ⟨k, rfl⟩
    exact RingHom.mem_ker.1 this
  have hcomm : (q.comp p).comp σ = q.comp φ := by
    refine MvPolynomial.ringHom_ext (fun x => ?_) (fun k => ?_)
    · simp only [RingHom.comp_apply, σC, φC]
    · simp only [RingHom.comp_apply, σX, φX, qs, map_zero]
  have exi : ∀ (Q : Type) [CommRing Q] (a : A →+* Q) (b : E →+* Q),
      a.comp σ = b.comp φ → ∃ r : R →+* Q, r.comp (q.comp p) = a ∧ r.comp q = b := by
    intro Q _ a b h
    have hb : ∀ x, b (φ x) = a (σ x) := fun x => (RingHom.congr_fun h x).symm
    have hle : RingHom.ker q ≤ RingHom.ker b := by
      rw [ker]
      refine Ideal.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker]
      rw [← φX, hb, σX, map_zero]
    have lf : ∀ x, q.liftOfSurjective surj ⟨b, hle⟩ (q x) = b x :=
      fun x => RingHom.liftOfSurjective_comp_apply q surj ⟨b, hle⟩ x
    refine ⟨q.liftOfSurjective surj ⟨b, hle⟩, ?_, ?_⟩
    · refine RingHom.ext fun x => ?_
      rw [RingHom.comp_apply, RingHom.comp_apply, lf, ← φC, hb, σC]
    · exact RingHom.ext fun x => by rw [RingHom.comp_apply, lf]
  have uni : ∀ (Q : Type) [CommRing Q] (u v : R →+* Q), u.comp q = v.comp q → u = v := by
    intro Q _ u v h
    refine RingHom.ext fun x => ?_
    obtain ⟨w, rfl⟩ := surj x
    exact RingHom.congr_fun h w
  have hsq : CommRingCat.ofHom σ ≫ CommRingCat.ofHom (q.comp p) = CommRingCat.ofHom φ ≫ CommRingCat.ofHom q := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcomm]
  have hpo : IsPushout (CommRingCat.ofHom σ) (CommRingCat.ofHom φ) (CommRingCat.ofHom (q.comp p))
      (CommRingCat.ofHom q) := by
    have ex' : ∀ t : PushoutCocone (CommRingCat.ofHom σ) (CommRingCat.ofHom φ),
        ∃ r : R →+* t.pt, r.comp (q.comp p) = t.inl.hom ∧ r.comp q = t.inr.hom := fun t =>
      exi t.pt t.inl.hom t.inr.hom (congrArg CommRingCat.Hom.hom t.condition)
    refine ⟨⟨hsq⟩, ⟨PushoutCocone.IsColimit.mk _
      (fun t => CommRingCat.ofHom (Classical.choose (ex' t))) ?_ ?_ ?_⟩⟩
    · intro t
      exact CommRingCat.hom_ext (Classical.choose_spec (ex' t)).1
    · intro t
      exact CommRingCat.hom_ext (Classical.choose_spec (ex' t)).2
    · intro t m h1 h2
      refine CommRingCat.hom_ext (uni t.pt m.hom _ ?_)
      exact (congrArg CommRingCat.Hom.hom h2).trans (Classical.choose_spec (ex' t)).2.symm
  have hst : (RingHom.toMorphismProperty @RingHom.Etale).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2 RingHom.Etale.isStableUnderBaseChange
  exact (RingHom.toMorphismProperty @RingHom.Etale).of_isPushout hpo hφ

private theorem etale_iter {K E : Type} [CommRing K] [CommRing E] (s : K →+* E) {n D : ℕ}
    (x : Fin n → E) (t : Fin D → E) (h : (eval₂Hom s (Sum.elim x t)).Etale) :
    (eval₂Hom (eval₂Hom s x) t).Etale := by
  let e : MvPolynomial (Fin D) (MvPolynomial (Fin n) K) ≃+* MvPolynomial (Fin n ⊕ Fin D) K :=
    ((MvPolynomial.sumAlgEquiv K (Fin D) (Fin n)).symm.trans
      (MvPolynomial.renameEquiv K (Equiv.sumComm (Fin D) (Fin n)))).toRingEquiv
  have key : eval₂Hom (eval₂Hom s x) t = (eval₂Hom s (Sum.elim x t)).comp e.toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun k => ?_)
    · induction a using MvPolynomial.induction_on with
      | C c => simp [e]
      | add a b ha hb => simp_all
      | mul_X a i ha => simp_all [e]
    · simp [e]
  rw [key]
  exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective e.bijective) h

private theorem std_etale {K E : Type} [CommRing K] [CommRing E] {n D : ℕ}
    (p : MvPolynomial (Fin n) K →+* E) (y : Fin D → E) (h : (eval₂Hom p y).Etale) :
    (p.comp MvPolynomial.C).IsStandardSmoothOfRelativeDimension (D + n) := by
  have h0 := (RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero.1 h).comp (stdC _ D)
  rw [MvPolynomial.eval₂Hom_comp_C, Nat.zero_add] at h0
  exact h0.comp (stdC K n)

private theorem std_etale0 {K E : Type} [CommRing K] [CommRing E] {n : ℕ}
    (p : MvPolynomial (Fin n) K →+* E) (h : p.Etale) :
    (p.comp MvPolynomial.C).IsStandardSmoothOfRelativeDimension n := by
  have h0 := (RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero.1 h).comp (stdC K n)
  rwa [Nat.zero_add] at h0

private theorem std_pres {R B : Type} [CommRing R] [CommRing B] (f : R →+* B) {d : ℕ} (u : Fin (d + 1) → B) (k : Fin (d + 1))
    (S : Set (MvPolynomial (Fin (d + 1)) R)) (surj : Function.Surjective (eval₂Hom f u))
    (ker : RingHom.ker (eval₂Hom f u) = Ideal.span S) (hk : (X k - 1 : MvPolynomial (Fin (d + 1)) R) ∈ S)
    (hS : ∀ s ∈ S, s = X k - 1 ∨ s = 0) : f.IsStandardSmoothOfRelativeDimension d := by
  obtain ⟨h, hd⟩ : ∃ h : MvPolynomial (Fin (d + 1)) R →+* MvPolynomial (Fin d) R,
    h = eval₂Hom MvPolynomial.C (k.insertNth 1 X) := ⟨_, rfl⟩
  obtain ⟨g, gd⟩ : ∃ g : MvPolynomial (Fin d) R →+* B, g = eval₂Hom f (fun m => u (k.succAbove m)) := ⟨_, rfl⟩
  obtain ⟨ι, ιd⟩ : ∃ ι : MvPolynomial (Fin d) R →+* MvPolynomial (Fin (d + 1)) R,
    ι = eval₂Hom MvPolynomial.C (fun m => X (k.succAbove m)) := ⟨_, rfl⟩
  have hX : h (X k) = 1 := by rw [hd, eval₂Hom_X', Fin.insertNth_apply_same]
  have hXs : ∀ m, h (X (k.succAbove m)) = X m := fun m => by rw [hd, eval₂Hom_X', Fin.insertNth_apply_succAbove]
  have hC : ∀ a, h (MvPolynomial.C a) = MvPolynomial.C a := fun a => by rw [hd, eval₂Hom_C]
  have gC : ∀ a, g (MvPolynomial.C a) = f a := fun a => by rw [gd, eval₂Hom_C]
  have gX : ∀ m, g (X m) = u (k.succAbove m) := fun m => by rw [gd, eval₂Hom_X']
  have uk : u k = 1 := by
    have : (X k - 1 : MvPolynomial (Fin (d + 1)) R) ∈ RingHom.ker (eval₂Hom f u) := by
      rw [ker]; exact Ideal.subset_span hk
    have := RingHom.mem_ker.1 this
    rw [map_sub, map_one, eval₂Hom_X'] at this
    exact sub_eq_zero.1 this
  have gh : g.comp h = eval₂Hom f u := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun m => ?_)
    · rw [RingHom.comp_apply, hC, gC, eval₂Hom_C]
    · rw [RingHom.comp_apply, eval₂Hom_X']
      rcases Fin.eq_self_or_eq_succAbove k m with rfl | ⟨m, rfl⟩
      · rw [hX, map_one, uk]
      · rw [hXs, gX]
  have hι : h.comp ι = RingHom.id _ := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun m => ?_)
    · simp [ιd, hC]
    · simp [ιd, hXs]
  have gι : (eval₂Hom f u).comp ι = g := by rw [← gh, RingHom.comp_assoc, hι, RingHom.comp_id]
  have hker : RingHom.ker (eval₂Hom f u) ≤ RingHom.ker h := by
    rw [ker]
    refine Ideal.span_le.2 fun s hs => ?_
    rcases hS s hs with rfl | rfl
    · simp [RingHom.mem_ker, hX]
    · simp
  have bij : Function.Bijective g := by
    refine ⟨(injective_iff_map_eq_zero g).2 fun a ha => ?_, fun b => ?_⟩
    · have h1 : ι a ∈ RingHom.ker (eval₂Hom f u) := by
        rw [RingHom.mem_ker]
        have := RingHom.congr_fun gι a
        rw [RingHom.comp_apply] at this
        rw [this, ha]
      have h2 := RingHom.mem_ker.1 (hker h1)
      have h3 := RingHom.congr_fun hι a
      rw [RingHom.comp_apply] at h3
      rw [h2] at h3
      exact h3.symm
    · obtain ⟨w, rfl⟩ := surj b
      exact ⟨h w, by rw [← RingHom.comp_apply, gh]⟩
  have e : f = (RingEquiv.ofBijective g bij).toRingHom.comp MvPolynomial.C := by
    ext a
    simp [gC]
  rw [e]
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _ _ (stdC R d)

private theorem etale_chart {A E B : Type} [CommRing A] [CommRing E] [CommRing B] {D : ℕ}
    (p : A →+* E) (ψ : E →+* B) (s : Fin D → E) (y : Fin D → B) (j : Fin D)
    (hφ : (eval₂Hom p s).Etale)
    (surj : Function.Surjective (eval₂Hom ψ y))
    (ker : RingHom.ker (eval₂Hom ψ y) = Ideal.span (insert (X j - 1 : MvPolynomial (Fin D) E)
      (Set.range fun k => MvPolynomial.C (s k) - MvPolynomial.C (s j) * X k))) :
    (eval₂Hom (ψ.comp p) (Function.update y j (ψ (s j)))).Etale := by
  classical
  obtain ⟨φ, hφd⟩ : ∃ φ : MvPolynomial (Fin D) A →+* E, φ = eval₂Hom p s := ⟨_, rfl⟩
  obtain ⟨f, hfd⟩ : ∃ f : MvPolynomial (Fin D) E →+* B, f = eval₂Hom ψ y := ⟨_, rfl⟩
  obtain ⟨g, hgd⟩ : ∃ g : MvPolynomial (Fin D) A →+* B,
    g = eval₂Hom (ψ.comp p) (Function.update y j (ψ (s j))) := ⟨_, rfl⟩
  obtain ⟨σ, hσd⟩ : ∃ σ : MvPolynomial (Fin D) A →+* MvPolynomial (Fin D) A,
    σ = eval₂Hom MvPolynomial.C (fun k => if k = j then X j else X k * X j) := ⟨_, rfl⟩
  rw [← hφd] at hφ
  rw [← hfd] at surj ker
  rw [← hgd]
  have φC : ∀ x, φ (MvPolynomial.C x) = p x := fun x => by rw [hφd, eval₂Hom_C]
  have φX : ∀ k, φ (X k) = s k := fun k => by rw [hφd, eval₂Hom_X']
  have fC : ∀ x, f (MvPolynomial.C x) = ψ x := fun x => by rw [hfd, eval₂Hom_C]
  have fX : ∀ k, f (X k) = y k := fun k => by rw [hfd, eval₂Hom_X']
  have gC : ∀ x, g (MvPolynomial.C x) = ψ (p x) := fun x => by rw [hgd, eval₂Hom_C]; rfl
  have gX : ∀ k, k ≠ j → g (X k) = y k := fun k hk => by
    rw [hgd, eval₂Hom_X', Function.update_of_ne hk]
  have gXj : g (X j) = ψ (s j) := by rw [hgd, eval₂Hom_X', Function.update_self]
  have σC : ∀ x, σ (MvPolynomial.C x) = MvPolynomial.C x := fun x => by rw [hσd, eval₂Hom_C]
  have σX : ∀ k, k ≠ j → σ (X k) = X k * X j := fun k hk => by
    rw [hσd, eval₂Hom_X', if_neg hk]
  have σXj : σ (X j) = X j := by rw [hσd, eval₂Hom_X', if_pos rfl]
  have mem1 : (X j - 1 : MvPolynomial (Fin D) E) ∈ RingHom.ker f := by
    rw [ker]; exact Ideal.subset_span (Set.mem_insert _ _)
  have mem2 : ∀ k, (MvPolynomial.C (s k) - MvPolynomial.C (s j) * X k : MvPolynomial (Fin D) E) ∈
      RingHom.ker f := fun k => by
    rw [ker]; exact Ideal.subset_span (Set.mem_insert_of_mem _ ⟨k, rfl⟩)
  have hyj : y j = 1 := by
    have := RingHom.mem_ker.1 mem1
    rw [map_sub, map_one, fX] at this
    exact sub_eq_zero.1 this
  have hsk : ∀ k, ψ (s k) = ψ (s j) * y k := fun k => by
    have := RingHom.mem_ker.1 (mem2 k)
    rw [map_sub, map_mul, fC, fC, fX] at this
    exact sub_eq_zero.1 this
  have hcomm : g.comp σ = ψ.comp φ := by
    refine MvPolynomial.ringHom_ext (fun x => ?_) (fun k => ?_)
    · simp only [RingHom.comp_apply, σC, gC, φC]
    · simp only [RingHom.comp_apply, φX]
      by_cases hk : k = j
      · subst hk; rw [σXj, gXj]
      · rw [σX k hk, map_mul, gX k hk, gXj, hsk k, mul_comm]
  have exi : ∀ (Q : Type) [CommRing Q] (a : MvPolynomial (Fin D) A →+* Q) (b : E →+* Q),
      a.comp σ = b.comp φ → ∃ r : B →+* Q, r.comp g = a ∧ r.comp ψ = b := by
    intro Q _ a b h
    have hb : ∀ x, b (φ x) = a (σ x) := fun x => (RingHom.congr_fun h x).symm
    obtain ⟨r', hr'⟩ : ∃ r' : MvPolynomial (Fin D) E →+* Q,
      r' = eval₂Hom b (Function.update (fun k => a (X k)) j 1) := ⟨_, rfl⟩
    have r'C : ∀ x, r' (MvPolynomial.C x) = b x := fun x => by rw [hr', eval₂Hom_C]
    have r'X : ∀ k, k ≠ j → r' (X k) = a (X k) := fun k hk => by
      rw [hr', eval₂Hom_X', Function.update_of_ne hk]
    have r'Xj : r' (X j) = 1 := by rw [hr', eval₂Hom_X', Function.update_self]
    have bs : ∀ k, b (s k) = a (σ (X k)) := fun k => by rw [← hb, φX]
    have hle : RingHom.ker f ≤ RingHom.ker r' := by
      rw [ker]
      refine Ideal.span_le.2 ?_
      rintro _ (rfl | ⟨k, rfl⟩)
      · simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, r'Xj, sub_self]
      · simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, r'C]
        by_cases hk : k = j
        · subst hk; rw [r'Xj, mul_one, sub_self]
        · rw [r'X k hk, bs k, bs j, σX k hk, σXj, map_mul, mul_comm, sub_self]
    refine ⟨f.liftOfSurjective surj ⟨r', hle⟩, ?_, ?_⟩
    · have lf : ∀ x, f.liftOfSurjective surj ⟨r', hle⟩ (f x) = r' x :=
        fun x => RingHom.liftOfSurjective_comp_apply f surj ⟨r', hle⟩ x
      refine MvPolynomial.ringHom_ext (fun x => ?_) (fun k => ?_)
      · rw [RingHom.comp_apply, gC, ← fC, lf, r'C, ← φC, hb, σC]
      · rw [RingHom.comp_apply]
        by_cases hk : k = j
        · subst hk; rw [gXj, ← fC, lf, r'C, bs, σXj]
        · rw [gX k hk, ← fX, lf, r'X k hk]
    · refine RingHom.ext fun x => ?_
      rw [RingHom.comp_apply, ← fC, RingHom.liftOfSurjective_comp_apply f surj ⟨r', hle⟩, r'C]
  have uni : ∀ (Q : Type) [CommRing Q] (u v : B →+* Q),
      u.comp g = v.comp g → u.comp ψ = v.comp ψ → u = v := by
    intro Q _ u v h1 h2
    have h3 : u.comp f = v.comp f := by
      refine MvPolynomial.ringHom_ext (fun x => ?_) (fun k => ?_)
      · simpa only [RingHom.comp_apply, fC] using RingHom.congr_fun h2 x
      · rw [RingHom.comp_apply, RingHom.comp_apply, fX]
        by_cases hk : k = j
        · subst hk; rw [hyj, map_one, map_one]
        · simpa only [RingHom.comp_apply, gX k hk] using RingHom.congr_fun h1 (X k)
    refine RingHom.ext fun x => ?_
    obtain ⟨w, rfl⟩ := surj x
    exact RingHom.congr_fun h3 w
  have hsq : CommRingCat.ofHom σ ≫ CommRingCat.ofHom g = CommRingCat.ofHom φ ≫ CommRingCat.ofHom ψ := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcomm]
  have hpo : IsPushout (CommRingCat.ofHom σ) (CommRingCat.ofHom φ) (CommRingCat.ofHom g)
      (CommRingCat.ofHom ψ) := by
    have ex' : ∀ t : PushoutCocone (CommRingCat.ofHom σ) (CommRingCat.ofHom φ),
        ∃ r : B →+* t.pt, r.comp g = t.inl.hom ∧ r.comp ψ = t.inr.hom := fun t =>
      exi t.pt t.inl.hom t.inr.hom (congrArg CommRingCat.Hom.hom t.condition)
    refine ⟨⟨hsq⟩, ⟨PushoutCocone.IsColimit.mk _
      (fun t => CommRingCat.ofHom (Classical.choose (ex' t))) ?_ ?_ ?_⟩⟩
    · intro t
      exact CommRingCat.hom_ext (Classical.choose_spec (ex' t)).1
    · intro t
      exact CommRingCat.hom_ext (Classical.choose_spec (ex' t)).2
    · intro t m h1 h2
      refine CommRingCat.hom_ext (uni t.pt m.hom _ ?_ ?_)
      · exact (congrArg CommRingCat.Hom.hom h1).trans (Classical.choose_spec (ex' t)).1.symm
      · exact (congrArg CommRingCat.Hom.hom h2).trans (Classical.choose_spec (ex' t)).2.symm
  have hst : (RingHom.toMorphismProperty @RingHom.Etale).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2 RingHom.Etale.isStableUnderBaseChange
  exact (RingHom.toMorphismProperty @RingHom.Etale).of_isPushout hpo hφ

private theorem ofPts {X Y : Scheme.{0}} (f : X ⟶ Y) (n : ℕ)
    (H : ∀ x : X, ∃ O : X.Opens, x ∈ O ∧ SmoothOfRelativeDimension n (O.ι ≫ f)) :
    SmoothOfRelativeDimension n f := by
  have hL : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} n) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))
  choose O hx hO using H
  refine (IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @SmoothOfRelativeDimension n) O ?_).2 hO
  exact top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hx x⟩

private theorem chart {X Y : Scheme.{0}} (f : X ⟶ Y) (n : ℕ) {U : Y.Opens} {V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (h : RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U V e).hom) :
    SmoothOfRelativeDimension n (V.ι ≫ f) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have hr := RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)
  have h1 : SmoothOfRelativeDimension n (f.resLE U V e) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)]
    exact ((RingHom.locally_respectsIso hr).arrow_mk_iso_iff (arrowResLEAppIso f U V e)).mpr
      (RingHom.locally_of hr _ h)
  have h2 : SmoothOfRelativeDimension (n + 0) (f.resLE U V e ≫ U.ι) := inferInstance
  rw [Scheme.Hom.resLE_comp_ι] at h2
  exact h2

private theorem dim_unique {X Y : Scheme.{0}} (f : X ⟶ Y) {a b : ℕ} (x : X)
    (ha : SmoothOfRelativeDimension a f) (hb : SmoothOfRelativeDimension b f) : a = b := by
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := ha.exists_isStandardSmoothOfRelativeDimension x
  have hl : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension b) (f.appLE U V e).hom :=
    HasRingHomProperty.appLE (@SmoothOfRelativeDimension b) f hb ⟨U, hU⟩ ⟨V, hV⟩ e
  obtain ⟨s, hs, hl⟩ := hl
  haveI : Nonempty V := ⟨⟨x, hx⟩⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal Γ(X, V)
  obtain ⟨t, ht, htm⟩ : ∃ t ∈ s, t ∉ m := by
    by_contra hc
    push_neg at hc
    exact hm.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 hc))
  have h1 := hl t ht
  have h0 : (algebraMap Γ(X, V) (Localization.Away t)).IsStandardSmoothOfRelativeDimension 0 :=
    RingHom.isStandardSmoothOfRelativeDimension_holdsForLocalizationAway _ t
  have h2 := h0.comp h
  rw [Nat.zero_add] at h2
  haveI : Nontrivial (Localization.Away t) := by
    letI := Ideal.Quotient.field m
    have hu : IsUnit (Ideal.Quotient.mk m t) :=
      isUnit_iff_ne_zero.2 (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    exact RingHom.domain_nontrivial (IsLocalization.Away.lift (S := Localization.Away t) t hu)
  letI := ((algebraMap Γ(X, V) (Localization.Away t)).comp (f.appLE U V e).hom).toAlgebra
  haveI ia : Algebra.IsStandardSmoothOfRelativeDimension a Γ(Y, U) (Localization.Away t) := h2
  haveI ib : Algebra.IsStandardSmoothOfRelativeDimension b Γ(Y, U) (Localization.Away t) := h1
  have ra := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := Γ(Y, U)) (S := Localization.Away t) a
  have rb := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := Γ(Y, U)) (S := Localization.Away t) b
  exact Nat.cast_injective (R := Cardinal) (ra.symm.trans rb)

section Charts

variable {K : Type} [CommRing K]

private theorem strV_comp {X X' : Scheme.{0}} (f : X ⟶ X') (q : X' ⟶ Spec (CommRingCat.of K)) (V' : X'.Opens)
    (V : X.Opens) (e : V ≤ f ⁻¹ᵁ V') : Pb.strV (f ≫ q) V = (f.appLE V' V e).hom.comp (Pb.strV q V') := by
  have h := Scheme.Hom.appLE_comp_appLE f q ⊤ V' V le_top e
  unfold Pb.strV
  rw [← h]
  rfl

private theorem sm_of_strV {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (hV : IsAffineOpen V) (n : ℕ)
    (h : (Pb.strV q V).IsStandardSmoothOfRelativeDimension n) : SmoothOfRelativeDimension n (V.ι ≫ q) := by
  refine chart q n (isAffineOpen_top _) hV le_top ?_
  have e : (q.appLE ⊤ V le_top).hom =
      (Pb.strV q V).comp (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toRingHom := by
    refine RingHom.ext fun a => ?_
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv a) = a :=
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm_apply_apply a
    simp [Pb.strV, h2]
  rw [e]
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _ _ h

variable {W Z Y : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z) (π : Y ⟶ Z) {D : ℕ} {V : Z.Opens}

private theorem chartZ (c : CrystallineSemistableComparison.Onto.BChart p i π D V) : SmoothOfRelativeDimension (D + c.n) (V.ι ≫ p) := by
  refine sm_of_strV p V c.affine _ ?_
  have h := std_etale (eval₂Hom (Pb.strV p V) c.x) c.t (etale_iter _ _ _ c.etale)
  rwa [eval₂Hom_comp_C] at h

private theorem chartY (c : CrystallineSemistableComparison.Onto.BChart p i π D V) (k : Fin D) :
    SmoothOfRelativeDimension (D + c.n) ((c.C k).ι ≫ π ≫ p) := by
  refine sm_of_strV _ _ (c.C_aff k) _ ?_
  have h1 := etale_chart (eval₂Hom (Pb.strV p V) c.x) (π.appLE V (c.C k) (c.C_le k)).hom c.t (c.u k) k
    (etale_iter _ _ _ c.etale) (c.surj k) (c.rel k)
  have h := std_etale _ _ h1
  rw [RingHom.comp_assoc, eval₂Hom_comp_C, ← strV_comp π p V _ (c.C_le k)] at h
  exact h

private theorem chartT {T : Scheme.{0}} [IsClosedImmersion i] {d : ℕ} (c : CrystallineSemistableComparison.Onto.BChart p i π (d + 1) V) (k : Fin (d + 1))
    (j : T ⟶ Y) (r : T ⟶ W) (hpb : IsPullback j r π i) :
    SmoothOfRelativeDimension (d + c.n) ((j ⁻¹ᵁ c.C k).ι ≫ j ≫ π ≫ p) := by
  have hVi : IsAffineOpen (i ⁻¹ᵁ V) := c.affine.preimage i
  have h' : j ⁻¹ᵁ c.C k ≤ r ⁻¹ᵁ (i ⁻¹ᵁ V) := by
    intro y hy
    have h1 : π (j y) ∈ V := c.C_le k hy
    have e : π (j y) = i (r y) := by
      have := congr($(hpb.w) y)
      simpa only [Scheme.Hom.comp_apply] using this
    change i (r y) ∈ V
    rwa [← e]
  obtain ⟨hA, hs, hker⟩ := presBC π r i j hpb V (c.C k) (c.C_le k) c.affine (c.C_aff k) hVi h' (Fin (d + 1)) (c.u k) _
    (c.surj k) (c.rel k)
  have ht : ∀ m, (i.app V).hom (c.t m) = 0 := fun m => by
    have : c.t m ∈ RingHom.ker (i.app V).hom := by
      rw [c.ker]
      exact Ideal.subset_span ⟨m, rfl⟩
    exact RingHom.mem_ker.1 this
  have hstd : (r.appLE (i ⁻¹ᵁ V) (j ⁻¹ᵁ c.C k) h').hom.IsStandardSmoothOfRelativeDimension d := by
    refine std_pres _ _ k _ hs hker ⟨X k - 1, Set.mem_insert _ _, by simp⟩ ?_
    rintro _ ⟨s, (rfl | ⟨m, rfl⟩), rfl⟩
    · left
      simp
    · right
      simp [ht]
  have hq : ((i.app V).hom.comp (eval₂Hom (Pb.strV p V) c.x)).Etale :=
    etale_quot _ _ c.t (etale_iter _ _ _ c.etale) (i.app_surjective V c.affine) c.ker
  have hW := std_etale0 _ hq
  rw [RingHom.comp_assoc, eval₂Hom_comp_C] at hW
  have hW' : (Pb.strV (i ≫ p) (i ⁻¹ᵁ V)).IsStandardSmoothOfRelativeDimension c.n := by
    rw [strV_comp i p V _ le_rfl, Scheme.Hom.appLE_eq_app]
    exact hW
  have hc := hstd.comp hW'
  rw [← strV_comp r (i ≫ p) (i ⁻¹ᵁ V) _ h'] at hc
  have hm := sm_of_strV _ _ hA _ hc
  have hw : j ≫ π ≫ p = r ≫ i ≫ p := by rw [← Category.assoc, hpb.w, Category.assoc]
  rw [hw]
  exact hm

end Charts

theorem blowE : BlowE := by
  intro K _ W Z Y T p i π D d e hB hsm hpr j r hpb
  obtain ⟨B⟩ := hB
  haveI := B.closed
  have hcl : IsClosedImmersion j := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip B.closed
  have hr : IsProper r := MorphismProperty.of_isPullback (P := @IsProper) hpb hpr
  have find : ∀ y : Y, π y ∈ Set.range i → ∃ (α : B.ι) (k : Fin (d + 1)), y ∈ (B.c α).C k ∧ π y ∈ B.V α := by
    rintro y ⟨w, hw⟩
    have h1 : w ∈ i ⁻¹ᵁ (⨆ α, B.V α) := B.cover (show w ∈ (⊤ : W.Opens) from trivial)
    obtain ⟨α, hα⟩ := TopologicalSpace.Opens.mem_iSup.1 (show i w ∈ ⨆ α, B.V α from h1)
    have h2 : π y ∈ B.V α := hw ▸ hα
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 ((B.c α).C_cover (show y ∈ π ⁻¹ᵁ B.V α from h2))
    exact ⟨α, k, hk, h2⟩
  have dimE : ∀ (α : B.ι) (z : Z), z ∈ B.V α → (B.c α).n = e := by
    intro α z hz
    have h1 := chartZ p i π (B.c α)
    have h2 : SmoothOfRelativeDimension (0 + (e + (d + 1))) ((B.V α).ι ≫ p) := inferInstance
    have := dim_unique ((B.V α).ι ≫ p) (⟨z, hz⟩ : (B.V α : Scheme.{0})) h1 h2
    omega
  refine ⟨⟨hcl, ?_, ?_⟩, hr⟩
  · refine ofPts _ _ fun y => ?_
    by_cases hy : π y ∈ B.U
    · refine ⟨π ⁻¹ᵁ B.U, hy, ?_⟩
      haveI := B.iso
      have h0 : SmoothOfRelativeDimension (0 + (0 + (e + (d + 1)))) ((π ∣_ B.U) ≫ B.U.ι ≫ p) := inferInstance
      rw [Nat.zero_add, Nat.zero_add, ← Category.assoc, morphismRestrict_ι, Category.assoc] at h0
      exact h0
    · have hrange : π y ∈ Set.range i := by
        by_contra h
        apply hy
        change π y ∈ (B.U : Set Z)
        rw [B.U_eq]
        exact h
      obtain ⟨α, k, hk, hv⟩ := find y hrange
      refine ⟨_, hk, ?_⟩
      have h1 := chartY p i π (B.c α) k
      rw [dimE α _ hv] at h1
      have he : d + 1 + e = e + d + 1 := by omega
      rw [he] at h1
      exact h1
  · refine ofPts _ _ fun t => ?_
    have hrange : π (j t) ∈ Set.range i := ⟨r t, by
      have := congr($(hpb.w) t)
      simpa only [Scheme.Hom.comp_apply] using this.symm⟩
    obtain ⟨α, k, hk, hv⟩ := find (j t) hrange
    refine ⟨j ⁻¹ᵁ (B.c α).C k, hk, ?_⟩
    have h1 := chartT p i π (B.c α) k j r hpb
    rw [dimE α _ hv, Nat.add_comm] at h1
    exact h1

end UpperTheory.Gal.KunnethLefschetz.G
