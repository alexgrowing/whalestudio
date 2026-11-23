import Formalism.LocalToGlobal.Columns.TiedVal

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct Pointwise

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

namespace GSD.Ev

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K} {σ : K →+* ℂ} (E : S.Ev σ)

theorem ev_injective : Function.Injective E.ev := by
  intro x y h
  rw [E.ev_eq_lin x, E.ev_eq_lin y] at h
  have h1 := (LinearMap.ker_eq_bot.1 E.lin_ker) h
  apply S.bV.repr.injective
  ext i
  exact σ.injective (congrFun h1 i)

theorem tr_of_mem_Fi {φ : S.Cl → E.Y → ℂ} (hφ : φ ∈ E.Fi) (c : S.Cl) (g : S.G) (hg : g • S.outSec.rep c = S.outSec.rep c) :
    E.tr g (φ c) = φ c := by
  unfold GSD.Ev.Fi at hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ψ, rfl⟩ := hx
    rw [E.emb_apply, E.tr_ev, ← ψ.2 g, hg]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [Pi.add_apply, map_add, hx, hy]
  | smul a x _ hx => rw [Pi.smul_apply, map_smul, hx]

theorem exists_emb_iff (h : S.Ok) (φ : S.Cl → E.Y → ℂ) :
    (∃ x, E.emb x = φ) ↔ φ ∈ E.Fi ∧ ∀ c, ∃ v : S.V, φ c = E.ev v := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Submodule.subset_span ⟨x, rfl⟩, fun c => ⟨_, E.emb_apply x c⟩⟩
  · rintro ⟨hφ, hv⟩
    choose v hv using hv
    have hinv : v ∈ (S.toCSDOf h S.outSec).Forms := by
      intro c γ
      apply E.ev_injective
      show E.ev (S.ρ (γ : S.G) (v c)) = E.ev (v c)
      rw [← E.tr_ev, ← hv c]
      exact E.tr_of_mem_Fi hφ c γ γ.2
    refine ⟨(S.resOf h S.outSec).symm ⟨v, hinv⟩, ?_⟩
    funext c
    rw [E.emb_apply, hv c]
    congr 1
    exact congrFun (congrArg Subtype.val ((S.resOf h S.outSec).apply_symm_apply ⟨v, hinv⟩)) c

end GSD.Ev

section Pol

variable {K : Type} [Field K] (s : K →+* ℂ) {ι : Type} [Fintype ι] {n : ℕ}

theorem smul_mem_RatSpanG (lam : ι → DomWeight n) (r : K) {p : MvPolynomial (ι × Fin n × Fin n) ℂ}
    (hp : p ∈ RatSpanG s lam) : s r • p ∈ RatSpanG s lam := by
  unfold RatSpanG at hp ⊢
  induction hp using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r', f, hf, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨r * r', f, hf, ?_⟩
    rw [smul_smul, map_mul]
  | zero => rw [smul_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [smul_neg]; exact AddSubgroup.neg_mem _ hx

theorem RatSpanG_shW (lam : ι → DomWeight n) (c : ι → ℤ) :
    RatSpanG s (fun τ => shW (lam τ) (c τ)) = RatSpanG s lam := by
  unfold RatSpanG
  simp only [delSq_shW]

theorem exists_VV_of_mem_RatSpanG (lam : ι → DomWeight n) {p : MvPolynomial (ι × Fin n × Fin n) ℂ}
    (hp : p ∈ RatSpanG s lam) : ∃ F ∈ VV K lam, MvPolynomial.map s F = p := by
  unfold RatSpanG at hp
  induction hp using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, f, hf, rfl⟩ := hx
    refine ⟨r • ∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (MvPolynomial.map (Int.castRingHom K) (f τ)), ?_, ?_⟩
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, fun τ => ?_, rfl⟩)
      exact Formalism.GradedWeylDivisibility.weylLeDual K n n le_rfl _ (natW_anti (lam τ)) (map_mem_weyl le_rfl _ _ (hf τ))
    · rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul, map_ten]
      congr 2
      funext τ
      rw [MvPolynomial.map_map]
      have e : s.comp (Int.castRingHom K) = Int.castRingHom ℂ := RingHom.ext_int _ _
      rw [e]
  | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨F, hF, rfl⟩ := hx
    obtain ⟨F', hF', rfl⟩ := hy
    exact ⟨F + F', Submodule.add_mem _ hF hF', map_add _ _ _⟩
  | neg x _ hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    exact ⟨-F, Submodule.neg_mem _ hF, map_neg _ _⟩

variable [CharZero K]

theorem map_mem_RatSpanG (lam : ι → DomWeight n) {F : MvPolynomial (ι × Fin n × Fin n) K} (hF : F ∈ VV K lam) :
    MvPolynomial.map s F ∈ RatSpanG s lam := by
  unfold VV Formalism.GradedWeylDivisibility.tensorLat at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    let T : ι → Set (MvPolynomial (ι × Fin n × Fin n) K) := fun τ =>
      Set.range fun w : List (Fin n × Fin n × ℕ) =>
        Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.applyWord K w (Formalism.GradedWeylDivisibility.hw K le_rfl (lam τ).natW))
    have h1 : ∀ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (f τ) ∈ Submodule.span K (T τ) := by
      intro τ
      have h0 : f τ ∈ delSq K n (lam τ) := by rw [← nablaSq_eq_delSq]; exact hf τ
      have h := Submodule.mem_map_of_mem (f := (Formalism.GradedWeylDivisibility.blockEmb K (k := n) (n := n) τ).toLinearMap) h0
      unfold delSq Formalism.GradedWeylDivisibility.weyl at h
      rw [Submodule.map_span, ← Set.range_comp] at h
      exact h
    have h2 : (∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (f τ)) ∈ Submodule.span K (∏ τ, T τ) := by
      rw [← Submodule.prod_span]
      exact prod_mem_prod_sub _ _ _ fun τ _ => h1 τ
    have key : ∀ y ∈ Submodule.span K (∏ τ, T τ), MvPolynomial.map s y ∈ RatSpanG s lam := by
     intro y hy
     induction hy using Submodule.span_induction with
     | mem y hy =>
      rw [Set.mem_finsetProd] at hy
      obtain ⟨g, hg, rfl⟩ := hy
      have hg' : ∀ τ, ∃ w : List (Fin n × Fin n × ℕ),
          Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.applyWord K w (Formalism.GradedWeylDivisibility.hw K le_rfl (lam τ).natW)) = g τ :=
        fun τ => hg (Finset.mem_univ τ)
      choose w hw using hg'
      refine AddSubgroup.subset_closure ⟨1, fun τ => Formalism.GradedWeylDivisibility.applyWord ℤ (w τ) (Formalism.GradedWeylDivisibility.hw ℤ le_rfl (lam τ).natW),
        fun τ => Submodule.subset_span ⟨w τ, rfl⟩, ?_⟩
      rw [map_one, one_smul]
      have e : (∏ τ, g τ) = ∏ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.applyWord K (w τ) (Formalism.GradedWeylDivisibility.hw K le_rfl (lam τ).natW)) :=
        Finset.prod_congr rfl fun τ _ => (hw τ).symm
      rw [e, map_ten]
      congr 1
      funext τ
      rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map, ← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map,
        Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
     | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
     | add y z _ _ hy hz => rw [map_add]; exact AddSubgroup.add_mem _ hy hz
     | smul c y _ hy =>
      rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
      exact smul_mem_RatSpanG s lam c hy
    exact key _ h2
  | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact AddSubgroup.add_mem _ hx hy
  | smul c x _ hx =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact smul_mem_RatSpanG s lam c hx

theorem mem_RatSpanG_iff (lam : ι → DomWeight n) (p : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    p ∈ RatSpanG s lam ↔ ∃ F ∈ VV K lam, MvPolynomial.map s F = p :=
  ⟨exists_VV_of_mem_RatSpanG s lam, by rintro ⟨F, hF, rfl⟩; exact map_mem_RatSpanG s lam hF⟩

end Pol

section Round

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem roundEv_exists_emb_iff (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
    (lam : X.Tau → DomWeight n) (L : DecoSet X.E n ST SG → Submodule (𝓞 X.E) (Sp X.E n)) (Λ : LevFam X.E X.K n SG)
    (h : (formGSD (roundPk X lam L) Λ).Ok) (φ : (formGSD (roundPk X lam L) Λ).Cl → FrS X σ₀ n → ℂ) :
    (∃ x, (roundEv σ₀ hσ lam L Λ).emb x = φ) ↔
      φ ∈ (roundEv σ₀ hσ lam L Λ).Fi ∧ ∀ c, ∃ P ∈ RatSpanG σ₀ lam, φ c = fnOf _ (shiftOf lam) 1 P := by
  rw [(roundEv σ₀ hσ lam L Λ).exists_emb_iff h φ]
  refine and_congr_right fun _ => forall_congr' fun c => ?_
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨_, map_mem_RatSpanG σ₀ lam (v : VV X.K lam).2, hv⟩
  · rintro ⟨P, hP, hv⟩
    obtain ⟨F, hF, rfl⟩ := exists_VV_of_mem_RatSpanG σ₀ lam hP
    exact ⟨(⟨F, hF⟩ : VV X.K lam), hv⟩

end Round

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
  (hX : X.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word) (i : ℕ)

include hX in

theorem Val.rat (Q : ValCrd W Λ σ₀ u i) : Val.Rat W Λ σ₀ hσ u i Q := by
  obtain ⟨⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩, lt, rfl⟩ := Q
  intro φ
  have h := roundEv_exists_emb_iff σ₀ hσ (W.lamTrue u i) (fun d : DecoSet X.E (R.N i) (Pr.vT u) Pr.vGs => d.1.Lsh) (Λ i)
    (stepOk W Λ hX u i) φ
  have e : RatSpanG σ₀ (W.lamTrue u i) = RatSpanG σ₀ (W.lamN u i) := by
    rw [lamTrue_eq_shW]
    exact RatSpanG_shW σ₀ _ _
  rw [e] at h
  refine h.trans (and_congr_right fun _ => forall_congr' fun c => ?_)
  constructor
  · rintro ⟨P, hP, hv⟩
    exact ⟨P, hP, fun z => congrFun hv z⟩
  · rintro ⟨P, hP, hv⟩
    exact ⟨P, hP, funext hv⟩

end Gen

end Formalism.L2.Col
