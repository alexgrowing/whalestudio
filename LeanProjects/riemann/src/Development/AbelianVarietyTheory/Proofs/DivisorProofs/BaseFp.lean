import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingRChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrob
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisibilityLatticeDescendsIntegralExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeComapFiniteProjectiveSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPresentationDescends
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPresentationBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBaseChangeIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenerators

set_option autoImplicit false

open GlobalTheory.RingChain GlobalTheory.PerfdLat
open scoped TensorProduct Pointwise

namespace GlobalTheory.RingChain.RingDesc

abbrev Cok {A : Type} [CommRing A] {m r : ℕ} (R : Matrix (Fin m) (Fin r) A) : Type :=
  (Fin m → A) ⧸ LinearMap.range (Matrix.mulVecLin R)

theorem mv_one {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) {h : ℕ} (x : Fin h → A) : mv g 1 x = piMap g _ x := by
  rw [mv, Matrix.map_one _ Int.cast_zero Int.cast_one, Matrix.one_mulVec]; rfl

theorem base_fp {A : Type} [CommRing A] [IsDomain A] {π : A} (hπ : π ≠ 0) (h : ℕ) :
    Module.Finite A (baseOf π h) ∧ Module.Projective A (baseOf π h) := by
  have e : (Fin h → A) ≃ₗ[A] baseOf π h :=
    (LinearEquiv.ofInjective (LinearMap.lsmul A (Fin h → A) π) (smul_right_injective _ hπ)).trans
      (LinearEquiv.ofEq _ _ (by
        ext x
        rw [Submodule.mem_smul_pointwise_iff_exists]
        exact ⟨fun ⟨y, e⟩ => ⟨y, trivial, e⟩, fun ⟨y, _, e⟩ => ⟨y, e⟩⟩))
  exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩

theorem frob (p : ℕ) [Fact p.Prime] (k : ℕ) {B : Type} [CommRing B] {m₁ r₁ m₂ r₂ : ℕ} {R₁ : Matrix (Fin m₁) (Fin r₁) B}
    {R₂ : Matrix (Fin m₂) (Fin r₂) B} {M N : Type} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    (e₁ : Cok R₁ ≃ₗ[B] M) (e₂ : Cok R₂ ≃ₗ[B] N) (ψ : M →+ N) (hψ : IsFrobLin B p (p ^ k) ψ) :
    ∃ T : Set B, T.Finite ∧ ∀ (A' : Type) [CommRing A'] (g : A' →+* B), Function.Injective g → T ⊆ Set.range g →
      ∀ (R₁' : Matrix (Fin m₁) (Fin r₁) A') (R₂' : Matrix (Fin m₂) (Fin r₂) A'), R₁'.map g = R₁ → R₂'.map g = R₂ →
      ∀ (M' N' : Type) [AddCommGroup M'] [Module A' M'] [AddCommGroup N'] [Module A' N'] (e₁' : Cok R₁' ≃ₗ[A'] M')
        (e₂' : Cok R₂' ≃ₗ[A'] N'), ∃ ψ' : M' →+ N', IsFrobLin A' p (p ^ k) ψ' ∧ ∀ x y,
          ψ' (e₁' (Submodule.Quotient.mk x)) = e₂' (Submodule.Quotient.mk y) →
          ψ (e₁ (Submodule.Quotient.mk (piMap g _ x))) = e₂ (Submodule.Quotient.mk (piMap g _ y)) := by
  have h1 := (GlobalTheory.RingChain.FrobLin.main B p _ _ _).2.2.2.2 _ _ e₂.symm ((GlobalTheory.RingChain.FrobLin.main B p _ _ _).2.2.2.1 _ e₁ ψ hψ)
  obtain ⟨T, hT, H⟩ := GlobalTheory.RingChain.MatFrob.main p k B _ _ _ _ R₁ R₂ _ h1
  refine ⟨T, hT, fun A' _ g hg hTg R₁' R₂' hR₁ hR₂ M' N' _ _ _ _ e₁' e₂' => ?_⟩
  obtain ⟨ψ', h2, h3⟩ := H A' g hg hTg R₁' R₂' hR₁ hR₂
  refine ⟨_, (GlobalTheory.RingChain.FrobLin.main A' p _ _ _).2.2.2.2 _ _ e₂' ((GlobalTheory.RingChain.FrobLin.main A' p _ _ _).2.2.2.1 _ e₁'.symm ψ' h2),
    fun x y hxy => ?_⟩
  have := h3 x y (e₂'.injective (by simpa using hxy))
  rw [← this]; simp

theorem pres {B : Type} [CommRing B] [IsDomain B] {h : ℕ} {ϖ : B} (P Q : Submodule B (Fin h → B)) (_ : Module.Finite B P)
    (_ : Module.Projective B P) (_ : Module.Finite B Q) (_ : Module.Projective B Q) (h0 : ϖ ≠ 0) (hQ : baseOf ϖ h ≤ Q)
    (hP : Q ≤ P) : ∃ (m r : ℕ) (R : Matrix (Fin m) (Fin r) B) (e : Cok R ≃ₗ[B] Qt P Q) (T : Set B), T.Finite ∧
      ∀ (A' : Type) [CommRing A'] [IsDomain A'] [IsIntegrallyClosed A'] (g : A' →+* B), Function.Injective g →
        g.IsIntegral → T ⊆ Set.range g → ∀ P' Q' : Submodule A' (Fin h → A'), (∀ x, x ∈ P' ↔ piMap g (Fin h) x ∈ P) →
          (∀ x, x ∈ Q' ↔ piMap g (Fin h) x ∈ Q) → ∃ (R' : Matrix (Fin m) (Fin r) A') (e' : Cok R' ≃ₗ[A'] Qt P' Q'),
            R'.map g = R ∧ ∀ (x : P') (x' : P), x'.1 = piMap g (Fin h) x.1 →
              ∃ c, e' (Submodule.Quotient.mk c) = Submodule.Quotient.mk x ∧
                e (Submodule.Quotient.mk (piMap g _ c)) = Submodule.Quotient.mk x' := by
  obtain ⟨m, r, u, R, e, T, he, hT, H⟩ := GlobalTheory.RingChain.exists_presentation_descends B h ϖ P Q h0 hQ hP
  refine ⟨m, r, R, e, T, hT, fun A' _ _ _ g hg hi hTg P' Q' hP' hQ' => ?_⟩
  obtain ⟨u', R', e', hu, hR, he'⟩ := H A' g hg hi hTg P' Q' hP' hQ'
  refine ⟨R', e', hR, fun x x' hx => ?_⟩
  obtain ⟨c, hc⟩ := e'.surjective (Submodule.Quotient.mk x)
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  refine ⟨c, hc, ?_⟩
  rw [he', Submodule.Quotient.eq, Submodule.mem_comap, hQ'] at hc
  rw [he, Submodule.Quotient.eq, Submodule.mem_comap]
  convert hc using 1
  simp [hx, map_sum, map_smulₛₗ, hu]

theorem presLie (p : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (Lie : Type) [AddCommGroup Lie] [Module A Lie]
    [Module.Finite A Lie] [Module.Projective A Lie] : ∃ (m r : ℕ) (R : Matrix (Fin m) (Fin r) B)
      (e : Cok R ≃ₗ[B] (B ⊗[A] Lie) ⧸ (p : B) • (⊤ : Submodule B (B ⊗[A] Lie))),
      ∀ (A' : Type) [CommRing A'] [Algebra A A'] (g : A' →+* B), (∀ a, g (algebraMap A A' a) = algebraMap A B a) →
        ∀ (Lie' : Type) [AddCommGroup Lie'] [Module A' Lie'] (eL : A' ⊗[A] Lie ≃ₗ[A'] Lie') (l : Lie' →ₛₗ[g] B ⊗[A] Lie),
          (∀ y, l (eL (1 ⊗ₜ y)) = 1 ⊗ₜ y) → ∃ (R' : Matrix (Fin m) (Fin r) A')
            (e' : Cok R' ≃ₗ[A'] Lie' ⧸ (p : A') • (⊤ : Submodule A' Lie')), R'.map g = R ∧ ∀ y : Lie',
              ∃ c, e' (Submodule.Quotient.mk c) = Submodule.Quotient.mk y ∧
                e (Submodule.Quotient.mk (piMap g _ c)) = Submodule.Quotient.mk (l y) := by
  obtain ⟨m, r, v, R, H⟩ := GlobalTheory.RingChain.exists_presentation_baseChange A p Lie
  obtain ⟨e, he⟩ := H B (B ⊗[A] Lie) (LinearEquiv.refl _ _) p _ (map_natCast _ _).symm rfl
  refine ⟨m, r, _, e, fun A' _ _ g hg Lie' _ _ eL l hl => ?_⟩
  obtain ⟨e', he'⟩ := H A' Lie' eL p _ (map_natCast _ _).symm rfl
  refine ⟨_, e', Matrix.ext fun i j => hg _, fun y => ?_⟩
  obtain ⟨c, hc⟩ := e'.surjective (Submodule.Quotient.mk y)
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  refine ⟨c, hc, ?_⟩
  rw [he', Submodule.Quotient.eq, Submodule.mem_smul_pointwise_iff_exists] at hc
  obtain ⟨z, -, hz⟩ := hc
  rw [he, Submodule.Quotient.eq, Submodule.mem_smul_pointwise_iff_exists]
  refine ⟨l z, trivial, ?_⟩
  have := congrArg l hz
  simpa [map_sum, map_smulₛₗ, hl] using this

theorem main : ∀ (p : ℕ) [Fact p.Prime] (A B : Type) [CommRing A] [CommRing B] [IsDomain B] [Algebra A B] [Algebra.IsIntegral A B] (h o : ℕ) (π : A) (γ : ℕ → A) (Lie Om : Type) [AddCommGroup Lie] [Module A Lie] [AddCommGroup Om] [Module A Om] [Module.Finite A Lie] [Module.Projective A Lie] [Module.Finite A Om] [Module.Projective A Om] (C : RChain p B h o (algebraMap A B π) (fun n => algebraMap A B (γ n)) (B ⊗[A] Lie) (B ⊗[A] Om)) (S : Set (Om × C.L 0)), S.Finite → algebraMap A B π ≠ 0 → (∀ s ∈ S, C.ρ (1 ⊗ₜ s.1) = Submodule.Quotient.mk (Submodule.Quotient.mk s.2)) → ∃ T : Set B, T.Finite ∧ ∀ (A' : Type) [CommRing A'] [IsDomain A'] [IsIntegrallyClosed A'] [Algebra A A'] (g : A' →+* B), Function.Injective g → (∀ a, g (algebraMap A A' a) = algebraMap A B a) → T ⊆ Set.range g → ∀ (π' : A') (γ' : ℕ → A'), π' = algebraMap A A' π → (∀ n, γ' n = algebraMap A A' (γ n)) → ∀ (Lie' Om' : Type) [AddCommGroup Lie'] [Module A' Lie'] [AddCommGroup Om'] [Module A' Om'] (eL : A' ⊗[A] Lie ≃ₗ[A'] Lie') (eO : A' ⊗[A] Om ≃ₗ[A'] Om'), ∃ (C' : RChain p A' h o π' γ' Lie' Om') (l : Lie' →ₛₗ[g] B ⊗[A] Lie) (m : Om' →ₛₗ[g] B ⊗[A] Om), (∀ y, l (eL (1 ⊗ₜ y)) = 1 ⊗ₜ y) ∧ (∀ w, m (eO (1 ⊗ₜ w)) = 1 ⊗ₜ w) ∧ (∀ n ≤ o, ∀ x, x ∈ C'.L n ↔ piMap g (Fin h) x ∈ C.L n) ∧ (∀ n, o < n → C'.L n = baseOf π' h) ∧ C'.Map C g 1 l m ∧ ∀ s ∈ S, ∃ x : C'.L 0, piMap g (Fin h) x.1 = s.2.1 ∧ C'.ρ (eO (1 ⊗ₜ s.1)) = Submodule.Quotient.mk (Submodule.Quotient.mk x) := by
  intro p _ A B _ _ _ _ _ h o π γ Lie Om _ _ _ _ _ _ _ _ C S hS h0 hρ
  have bf := base_fp h0 h
  haveI := C.finite
  haveI := C.projective
  choose T₁ hT₁ H₁ using fun n => GlobalTheory.RingChain.lattice_comap_finite_projective_span B h _ (C.L n) h0 (C.base_le n)
  choose m₂ r₂ R₂ e₂ T₂ hT₂ H₂ using fun n =>
    pres (C.L n) _ (C.finite n) (C.projective n) bf.1 bf.2 h0 le_rfl (C.base_le n)
  choose m₃ r₃ R₃ e₃ T₃ hT₃ H₃ using fun n =>
    pres (C.L n) (C.L (n + 1)) (C.finite n) (C.projective n) (C.finite _) (C.projective _) h0 (C.base_le _) (C.succ_le n)
  obtain ⟨m₄, r₄, R₄, e₄, H₄⟩ := presLie p A B Lie
  choose T₅ hT₅ H₅ using fun n : Fin o =>
    frob p 1 (e₂ (n + 1)) (e₂ n) (C.ψ n) (by rw [pow_one]; exact C.ψ_lin n n.2)
  choose T₆ hT₆ H₆ using fun n : Fin o => frob p (n + 1) (e₃ n) e₄ (C.κ n) (C.κ_lin n n.2)
  choose T₇ hT₇ H₇ using fun n : Fin o => GlobalTheory.CokerProj.projective_coker_descends B _ _ (R₃ n) (algebraMap A B (γ n)) (by
    haveI := C.lfree n n.2
    exact Module.Projective.of_equiv (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) (e₃ n).symm))
  obtain ⟨T₈, hT₈, H₈⟩ := GlobalTheory.MapDescent.maps_descend A B h _ (C.L 0) Lie Om C.j C.ρ S h0 (C.base_le 0) C.ρ_surj hS hρ
  refine ⟨(⋃ n : Fin (o + 1), T₁ n ∪ T₂ n ∪ T₃ n) ∪ (⋃ n : Fin o, T₅ n ∪ T₆ n ∪ T₇ n) ∪ T₈,
    ((Set.finite_iUnion fun n => ((hT₁ _).union (hT₂ _)).union (hT₃ _)).union
      (Set.finite_iUnion fun n => ((hT₅ _).union (hT₆ _)).union (hT₇ _))).union hT₈, ?_⟩
  intro A' _ _ _ _ g hg hc hT π' γ' hπ hγ Lie' Om' _ _ _ _ eL eO
  simp only [Set.union_subset_iff, Set.iUnion_subset_iff] at hT
  obtain ⟨⟨hTa, hTb⟩, hTc⟩ := hT
  have hi : g.IsIntegral := RingHom.IsIntegral.tower_top (algebraMap A A') g (by
    rw [show g.comp (algebraMap A A') = algebraMap A B from RingHom.ext hc]
    exact fun b => Algebra.IsIntegral.isIntegral b)
  have gπ : g π' = algebraMap A B π := by rw [hπ, hc]
  have gγ : ∀ n, g (γ' n) = algebraMap A B (γ n) := fun n => by rw [hγ, hc]
  have h0' : π' ≠ 0 := fun e => h0 (by rw [← gπ, e, map_zero])
  have hb : ∀ x, x ∈ baseOf π' h ↔ piMap g (Fin h) x ∈ baseOf (algebraMap A B π) h := fun x => by
    rw [← gπ]; exact ((GlobalTheory.RingChain.dvd_descends_of_isIntegral A' B g hg hi).2 h π' h0' x).symm
  obtain ⟨L, hL, hL', hfp⟩ : ∃ L : ℕ → Submodule A' (Fin h → A'), (∀ n ≤ o, ∀ x, x ∈ L n ↔ piMap g (Fin h) x ∈ C.L n) ∧
      (∀ n, o < n → L n = baseOf π' h) ∧ ∀ n, Module.Finite A' (L n) ∧ Module.Projective A' (L n) := by
    refine ⟨fun n => if n ≤ o then (C.L n).comap (piMap g (Fin h)) else baseOf π' h,
      fun n hn x => by simp only [if_pos hn]; rfl, fun n hn => if_neg (by omega), fun n => ?_⟩
    beta_reduce
    by_cases hn : n ≤ o
    · have := H₁ n A' g hg hi (hTa ⟨n, by omega⟩).1.1
      rw [show (if n ≤ o then (C.L n).comap (piMap g (Fin h)) else baseOf π' h) = _ from if_pos hn]
      exact ⟨this.1, this.2.1⟩
    · rw [show (if n ≤ o then (C.L n).comap (piMap g (Fin h)) else baseOf π' h) = _ from if_neg hn]
      exact base_fp h0' h
  have hmem : ∀ n, ∀ x ∈ L n, piMap g (Fin h) x ∈ C.L n := fun n x hx => by
    by_cases hn : n ≤ o
    · exact (hL n hn x).1 hx
    · rw [hL' n (by omega)] at hx
      exact C.base_le n ((hb x).1 hx)
  have hbase : ∀ n, baseOf π' h ≤ L n := fun n x hx => by
    by_cases hn : n ≤ o
    · exact (hL n hn x).2 (C.base_le n ((hb x).1 hx))
    · rwa [hL' n (by omega)]
  obtain ⟨j', ρ', l, m, hl, hm, hsurj, hj', hρ', hS'⟩ :=
    H₈ A' g hg hi hc hTc π' (L 0) gπ (hL 0 (Nat.zero_le o)) Lie' Om' eL eO
  obtain ⟨R₄', e₄', hR₄, he₄⟩ := H₄ A' g hc Lie' eL l hl
  have G₂ := fun n (hn : n ≤ o) => H₂ n A' g hg hi (hTa ⟨n, by omega⟩).1.2 (L n) _ (hL n hn) hb
  have G₃ := fun n (hn : n < o) => H₃ n A' g hg hi (hTa ⟨n, by omega⟩).2 (L n) (L (n + 1)) (hL n hn.le) (hL _ hn)
  have Gψ : ∀ n, ∃ ψ' : Qt (L (n + 1)) (baseOf π' h) →+ Qt (L n) (baseOf π' h), n < o → IsFrobLin A' p p ψ' ∧
      ∀ (x : L (n + 1)) (x' : C.L (n + 1)) (y : L n) (y' : C.L n), x'.1 = piMap g _ x.1 → y'.1 = piMap g _ y.1 →
        ψ' (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
          C.ψ n (Submodule.Quotient.mk x') = Submodule.Quotient.mk y' := fun n => by
    by_cases hn : n < o
    swap
    · exact ⟨0, fun k => absurd k hn⟩
    obtain ⟨R, e, hR, he⟩ := G₂ (n + 1) hn
    obtain ⟨R', e', hR', he'⟩ := G₂ n hn.le
    obtain ⟨ψ', k₁, k₂⟩ := H₅ ⟨n, hn⟩ A' g hg (hTb ⟨n, hn⟩).1.1 R R' hR hR' _ _ e e'
    refine ⟨ψ', fun _ => ⟨by rwa [pow_one] at k₁, fun x x' y y' hx hy k => ?_⟩⟩
    obtain ⟨c, c₁, c₂⟩ := he x x' hx
    obtain ⟨d, d₁, d₂⟩ := he' y y' hy
    rw [← c₂, ← d₂]
    exact k₂ c d (by rw [c₁, d₁, k])
  have Gκ : ∀ n, ∃ κ' : Qt (L n) (L (n + 1)) →+ Lie' ⧸ (p : A') • (⊤ : Submodule A' Lie'), n < o →
      IsFrobLin A' p (p ^ (n + 1)) κ' ∧ ∀ (x : L n) (x' : C.L n) (y : Lie'), x'.1 = piMap g _ x.1 →
        κ' (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
          C.κ n (Submodule.Quotient.mk x') = Submodule.Quotient.mk (l y) := fun n => by
    by_cases hn : n < o
    swap
    · exact ⟨0, fun k => absurd k hn⟩
    obtain ⟨R, e, hR, he⟩ := G₃ n hn
    obtain ⟨κ', k₁, k₂⟩ := H₆ ⟨n, hn⟩ A' g hg (hTb ⟨n, hn⟩).1.2 R R₄' hR hR₄ _ _ e e₄'
    refine ⟨κ', fun _ => ⟨k₁, fun x x' y hx k => ?_⟩⟩
    obtain ⟨c, c₁, c₂⟩ := he x x' hx
    obtain ⟨d, d₁, d₂⟩ := he₄ y
    rw [← c₂, ← d₂]
    exact k₂ c d (by rw [c₁, d₁, k])
  choose ψ' hψ' using Gψ
  choose κ' hκ' using Gκ
  refine ⟨{
      L := L
      finite := fun n => (hfp n).1
      projective := fun n => (hfp n).2
      base_le := hbase
      succ_le := fun n x hx => ?_
      kill := fun n hn x hx => ?_
      gam := fun n hn x hx => ?_
      lfree := fun n hn => ?_
      j := j'
      ρ := ρ'
      ρ_surj := hsurj
      ψ := ψ'
      ψ_lin := fun n hn => (hψ' n hn).1
      κ := κ'
      κ_lin := fun n hn => (hκ' n hn).1 }, l, m, hl, hm, hL, hL',
    ⟨fun n x hx => by rw [mv_one]; exact hmem n x hx, fun y x x' e => hj' y x x' (e.trans (mv_one g _)),
      fun y x x' e => hρ' y x x' (e.trans (mv_one g _)),
      fun n hn x x' y y' e e' => (hψ' n hn).2 x x' y y' (e.trans (mv_one g _)) (e'.trans (mv_one g _)),
      fun n hn x x' y e => (hκ' n hn).2 x x' y (e.trans (mv_one g _))⟩, hS'⟩
  · by_cases hn : n ≤ o
    · exact (hL n hn x).2 (C.succ_le n (hmem _ x hx))
    · rw [hL' _ (by omega)] at hx
      exact hbase n hx
  · obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    rw [hb, map_smulₛₗ, gγ]
    exact C.kill n hn (Submodule.smul_mem_pointwise_smul _ _ _ (hmem _ y hy))
  · obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    rw [hL _ hn, map_smulₛₗ, gγ]
    exact C.gam n hn (Submodule.smul_mem_pointwise_smul _ _ _ (hmem _ y hy))
  · obtain ⟨R, e, hR, -⟩ := G₃ n hn
    haveI := H₇ ⟨n, hn⟩ A' g hg (hTb ⟨n, hn⟩).2 R (γ' n) hR (gγ n)
    exact Module.Projective.of_equiv (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) e)

end GlobalTheory.RingChain.RingDesc
