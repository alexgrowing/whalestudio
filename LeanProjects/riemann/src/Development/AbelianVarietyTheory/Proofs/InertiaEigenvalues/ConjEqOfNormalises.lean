import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRowHeckeOfOcc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicRowLocalSplitExists
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteTypeSpannedBySplitPlaceLocalComponent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockTypeAtSplitPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalReciprocityUnramifiedSpherical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedVectorsNeBotOfMemSumIntertwiningRanges
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsParamFunVIffIsSysParamDOfLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatakeGLOfHasSatakeParametersPrincipalSeries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EOpEqAsAlgebraHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowSetFinite

noncomputable section

namespace GlobalTheory.TwInputs.Eig

section Abstract

open GlobalTheory.SphLabelOps

variable {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M]

theorem irr_of_scalar (ρ : G →* Module.End ℂ M) (S : Submodule ℂ M) (hS : ∀ g, ∀ x ∈ S, ρ g x ∈ S)
    (hirr : ∀ S' : Submodule ℂ M, S' ≤ S → (∀ g, ∀ x ∈ S', ρ g x ∈ S') → S' = ⊥ ∨ S' = S)
    (K Loc : Subgroup G) (hK : K ≤ Loc) (Away : Set G) (hdec : ∀ g, ∃ a ∈ Loc, ∃ b ∈ Away, g = a * b)
    (hcomm : ∀ a ∈ Loc, ∀ b ∈ Away, a * b = b * a)
    (R : G → Finset G) (hR : ∀ a ∈ Loc, Reps K a (R a)) {x : M} (hx : x ∈ S) (hxK : ∀ k ∈ K, ρ k x = x)
    (hc : ∀ a ∈ Loc, ∃ c : ℂ, ∑ γ ∈ R a, ρ γ x = c • x) (W' : Submodule ℂ M)
    (hle : W' ≤ Submodule.span ℂ {y | ∃ a ∈ Loc, y = ρ a x}) (hst : ∀ a ∈ Loc, ∀ y ∈ W', ρ a y ∈ W') :
    W' = ⊥ ∨ W' = Submodule.span ℂ {y | ∃ a ∈ Loc, y = ρ a x} := by
  classical
  set W := Submodule.span ℂ {y | ∃ a ∈ Loc, y = ρ a x} with hW
  have hWS : W ≤ S := Submodule.span_le.2 (by rintro _ ⟨a, -, rfl⟩; exact hS a x hx)
  by_cases h0 : W' = ⊥
  · exact Or.inl h0
  right

  have hfin : ∀ y ∈ W, (Set.range fun k : K => ρ k y).Finite := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      refine ((R a).finite_toSet.image fun γ => ρ γ x).subset ?_
      rintro _ ⟨k, rfl⟩
      obtain ⟨γ, ⟨h1, h2⟩, -⟩ := (hR a ha).2 (k * a) ⟨k, k.2, 1, one_mem _, by simp⟩
      refine ⟨γ, h1, ?_⟩
      have := hxK _ h2
      show ρ γ x = ρ k (ρ a x)
      rw [← this, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left, map_mul, Module.End.mul_apply, this]
    | zero => simp
    | add y z _ _ hy hz =>
      refine (hy.image2 (· + ·) hz).subset ?_
      rintro _ ⟨k, rfl⟩
      exact ⟨_, ⟨k, rfl⟩, _, ⟨k, rfl⟩, (map_add _ _ _).symm⟩
    | smul c y _ hy =>
      refine (hy.image (c • ·)).subset ?_
      rintro _ ⟨k, rfl⟩
      exact ⟨_, ⟨k, rfl⟩, (map_smul _ _ _).symm⟩

  have hline : ∀ y ∈ W, (∀ k ∈ K, ρ k y = y) → ∃ c : ℂ, y = c • x := by
    intro y hy hyK
    obtain ⟨f, t, ht, -, e⟩ := Submodule.mem_span_iff_exists_finset_subset.1 hy
    choose! a ha ea using fun u (hu : u ∈ t) => ht hu
    have e1 : y = ∑ u ∈ t, ρ (a u) (f u • x) := by
      rw [← e]
      exact Finset.sum_congr rfl fun u hu => by rw [map_smul, ← ea u hu]
    have e2 := GlobalTheory.SphScalar.avg ρ K t a (fun u => R (a u)) (fun u => f u • x) (fun u hu => hR _ (ha u hu))
      (fun u _ k hk => by rw [map_smul, hxK k hk]) (by rw [← e1]; exact hyK)
    choose! c hc using hc
    refine ⟨∑ u ∈ t, ((R (a u)).card : ℂ)⁻¹ * (f u * c (a u)), ?_⟩
    rw [e1, e2, Finset.sum_smul]
    refine Finset.sum_congr rfl fun u hu => ?_
    simp only [map_smul]
    rw [← Finset.smul_sum, hc _ (ha u hu), mul_smul, mul_smul]

  let O : Submodule ℂ M := Submodule.span ℂ {y | ∃ b ∈ Away, ∃ w ∈ W', y = ρ b w}
  have hO : O = S := by
    have hOS : O ≤ S := Submodule.span_le.2 (by rintro _ ⟨b, -, w, hw, rfl⟩; exact hS b w (hWS (hle hw)))
    have hmem : ∀ g, ∀ w ∈ W', ρ g w ∈ O := fun g w hw => by
      obtain ⟨a, ha, b, hb, rfl⟩ := hdec g
      rw [hcomm a ha b hb, map_mul, Module.End.mul_apply]
      exact Submodule.subset_span ⟨b, hb, _, hst a ha w hw, rfl⟩
    refine (hirr O hOS fun g y hy => ?_).resolve_left fun h => h0 ?_
    · have : O.map (ρ g) ≤ O := by
        rw [Submodule.map_span_le]
        rintro _ ⟨b, -, w, hw, rfl⟩
        rw [← Module.End.mul_apply, ← map_mul]
        exact hmem _ w hw
      exact this (Submodule.mem_map_of_mem hy)
    · rw [eq_bot_iff]
      intro w hw
      have := hmem 1 w hw
      rwa [map_one, Module.End.one_apply, h] at this
  obtain ⟨f, t, ht, -, e⟩ := Submodule.mem_span_iff_exists_finset_subset.1 (show x ∈ O from hO ▸ hx)
  choose! b hb w hw eb using fun u (hu : u ∈ t) => ht hu
  let ρK : K →* Module.End ℂ M := ρ.comp K.subtype
  let H : Subgroup K :=
    { carrier := {k | ∀ u ∈ t, ρK k (w u) = w u}
      one_mem' := fun u _ => by simp
      mul_mem' := fun {k l} hk hl u hu => by rw [map_mul, Module.End.mul_apply, hl u hu, hk u hu]
      inv_mem' := fun {k} hk u hu => by
        conv_lhs => rw [← hk u hu]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hq : Finite (K ⧸ H) := by
    have : ∀ u : t, Finite (Set.range fun k : K => ρ k (w u)) := fun u => hfin _ (hle (hw u u.2))
    refine Finite.of_injective (fun q : K ⧸ H => fun u : t =>
      (⟨ρ q.out (w u), q.out, rfl⟩ : Set.range fun k : K => ρ k (w u))) fun q q' h => ?_
    rw [← q.out_eq', ← q'.out_eq', QuotientGroup.eq]
    intro u hu
    have h1 : ρK q.out (w u) = ρK q'.out (w u) := congrArg Subtype.val (congrFun h ⟨u, hu⟩)
    rw [map_mul, Module.End.mul_apply, ← h1, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  letI : Fintype (K ⧸ H) := Fintype.ofFinite _
  have havW : ∀ y ∈ W', GlobalTheory.IsotSph.avg H ρK y ∈ W' := fun y hy => by
    simp only [GlobalTheory.IsotSph.avg, LinearMap.smul_apply, LinearMap.sum_apply]
    exact W'.smul_mem _ (W'.sum_mem fun q _ => hst _ (hK q.out.2) y hy)
  have hxW : x ∈ W' := by
    by_contra hx'
    have hz : ∀ u ∈ t, GlobalTheory.IsotSph.avg H ρK (w u) = 0 := fun u hu => by
      obtain ⟨c, hc⟩ := hline _ (hle (havW _ (hw u hu))) fun k hk =>
        GlobalTheory.IsotSph.avg_fixed H ρK (fun s hs => hs u hu) ⟨k, hk⟩
      by_cases h : c = 0
      · rw [hc, h, zero_smul]
      · exact absurd ((W'.smul_mem_iff h).1 (hc ▸ havW _ (hw u hu))) hx'
    apply hx'
    have h1 : GlobalTheory.IsotSph.avg H ρK x = x := GlobalTheory.IsotSph.avg_of_fixed H ρK fun k => hxK k k.2
    rw [← h1, ← e, map_sum]
    refine W'.sum_mem fun u hu => ?_
    rw [map_smul, eb u hu, ← GlobalTheory.IsotSph.avg_map H ρK ρK (ρ (b u)) fun k y => ?_, hz u hu, map_zero, smul_zero]
    · exact W'.zero_mem
    · show ρ (b u) (ρ k y) = ρ k (ρ (b u) y)
      rw [← Module.End.mul_apply, ← map_mul, ← hcomm _ (hK k.2) _ (hb u hu), map_mul, Module.End.mul_apply]
  exact le_antisymm hle (Submodule.span_le.2 (by rintro _ ⟨a, ha, rfl⟩; exact hst a ha x hxW))

end Abstract

section Descent

theorem descent {K H H' ι : Type} [Field K] [AddCommGroup H] [Module ℂ H] [AddCommGroup H'] [Module ℂ H'] {n : ℕ}
    (σ : K →+* ℂ) (j : (Fin n → K) →ₛₗ[σ] H)
    (hli : LinearIndependent ℂ fun k => j (Pi.basisFun K (Fin n) k)) (hsp : Submodule.span ℂ (Set.range j) = ⊤)
    (e : H →ₗ[ℂ] H') (he : Function.Injective e) (T : ι → Module.End K (Fin n → K)) (T' : ι → H →ₗ[ℂ] H')
    (hT : ∀ a x, e (j (T a x)) = T' a (j x)) {z : H} (hz : z ≠ 0) (hTz : ∀ a, T' a z = 0) :
    ∃ x, x ≠ 0 ∧ ∀ a, T a x = 0 := by
  classical
  have hj : ∀ x, j x = ∑ k, σ (x k) • j (Pi.basisFun K (Fin n) k) := fun x => by
    conv_lhs => rw [← (Pi.basisFun K (Fin n)).sum_repr x]
    simp [map_sum, map_smulₛₗ]
  have htop : ⊤ ≤ Submodule.span ℂ (Set.range fun k => j (Pi.basisFun K (Fin n) k)) := by
    rw [← hsp, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [hj]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let b := Module.Basis.mk hli htop
  have hb : ∀ k, b k = j (Pi.basisFun K (Fin n) k) := fun k => Module.Basis.mk_apply _ _ _
  have hrep : ∀ x k, b.repr (j x) k = σ (x k) := fun x k => by
    rw [hj]
    simp only [← hb]
    exact congrFun (b.repr_sum_self _) k
  letI : Algebra K ℂ := σ.toAlgebra
  obtain ⟨k0, hk0⟩ : ∃ k, b.repr z k ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (b.repr.map_eq_zero_iff.1 (Finsupp.ext h))
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K ℂ, φ (b.repr z k0) ≠ 0 := by
    by_contra h
    push Not at h
    exact hk0 ((Module.forall_dual_apply_eq_zero_iff K _).1 h)
  refine ⟨fun k => φ (b.repr z k), fun h => hφ (congrFun h k0), fun a => ?_⟩
  have h1 : ∑ k, b.repr z k • j (T a (Pi.basisFun K (Fin n) k)) = 0 := by
    apply he
    rw [map_zero, ← hTz a]
    conv_rhs => rw [← b.sum_repr z]
    simp only [map_sum, map_smul, hT, hb]
  funext l
  have h2 := congrArg (fun y => φ (b.repr y l)) h1
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, hrep, map_zero, Finsupp.zero_apply] at h2
  conv_lhs => rw [← (Pi.basisFun K (Fin n)).sum_repr fun k => φ (b.repr z k)]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, Pi.basisFun_repr]
  rw [Pi.zero_apply, ← h2]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_mul, smul_eq_mul, mul_comm, mul_comm (b.repr z k), ← smul_eq_mul, ← map_smul]
  rfl

end Descent

section Normaliser

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.LFun

theorem conj_eq_of_normalises {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (a : GL (Fin n) (w.adicCompletion E)) (ha : ∀ g ∈ KGL w n, a⁻¹ * g * a ∈ KGL w n) :
    ∃ k ∈ KGL w n, ∀ g, a⁻¹ * g * a = k⁻¹ * g * k := by
  classical
  have hm := @GlobalTheory.HeckeScalarSph.mem_GLint_iff n _ _ (Ov E w)
  by_cases hn : ∀ i j : Fin n, i = j
  · refine ⟨1, one_mem _, fun g => ?_⟩
    have : g * a = a * g := Units.ext (Matrix.ext fun i j => by
      simp only [Units.val_mul, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun k _ => by rw [hn j i, hn k i, mul_comm])
    rw [mul_assoc, this]; simp
  have hoff : ∀ i j : Fin n, i ≠ j → ∀ p q, (a⁻¹).1 p i * a.1 j q ∈ Ov E w := by
    intro i j hij p q
    have h2 : (Matrix.single i j (1 : w.adicCompletion E)) * Matrix.single i j (1 : w.adicCompletion E) = 0 :=
      Matrix.single_mul_single_of_ne _ _ _ _ hij.symm _
    let g : GL (Fin n) (w.adicCompletion E) := ⟨1 + Matrix.single i j 1, 1 - Matrix.single i j 1,
      by rw [add_mul, mul_sub, mul_sub, h2]; simp, by rw [sub_mul, mul_add, mul_add, h2]; simp⟩
    have h1 : ∀ p q, (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) p q ∈ Ov E w := fun p q => by
      rw [Matrix.one_apply]; split_ifs; exacts [one_mem _, zero_mem _]
    have hs : ∀ p q, Matrix.single i j (1 : w.adicCompletion E) p q ∈ Ov E w := fun p q => by
      rw [Matrix.single_apply]; split_ifs; exacts [one_mem _, zero_mem _]
    have hg : g ∈ KGL w n := hm.2 ⟨fun p q => add_mem (h1 p q) (hs p q), fun p q => sub_mem (h1 p q) (hs p q)⟩
    have h3 := sub_mem ((hm.1 (ha g hg)).1 p q) (h1 p q)
    have e : (a⁻¹ * g * a).1 = 1 + (a⁻¹).1 * Matrix.single i j 1 * a.1 := by
      rw [Units.val_mul, Units.val_mul]
      show (a⁻¹).1 * (1 + Matrix.single i j 1) * a.1 = _
      rw [mul_add, add_mul, mul_one, Units.inv_mul]
    rw [e, Matrix.add_apply, add_sub_cancel_left, Matrix.mul_apply, Finset.sum_eq_single j] at h3
    · simpa using h3
    · intro l _ hl
      rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hl, zero_mul]
    · simp
  have hall : ∀ i j p q : Fin n, (a⁻¹).1 p i * a.1 j q ∈ Ov E w := by
    intro i j p q
    by_cases hij : i = j
    swap
    · exact hoff i j hij p q
    subst hij
    obtain ⟨l, hl⟩ : ∃ l, l ≠ i := by
      by_contra h
      push Not at h
      exact hn fun x y => (h x).trans (h y).symm
    have h1 : ∑ m, a.1 l m * (a⁻¹).1 m l = 1 := by
      rw [← Matrix.mul_apply, Units.mul_inv, Matrix.one_apply_eq]
    rw [← mul_one ((a⁻¹).1 p i), ← h1, Finset.mul_sum, Finset.sum_mul]
    refine sum_mem fun m _ => ?_
    have := mul_mem (hoff i l hl.symm p m) (hoff l i hl m q)
    convert this using 1
    ring
  push Not at hn
  obtain ⟨i0, -⟩ := hn
  obtain ⟨⟨p, q⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n))
    (fun x => Valued.v (a.1 x.1 x.2)) ⟨(i0, i0), Finset.mem_univ _⟩
  have hc : a.1 p q ≠ 0 := fun h0 => by
    have hz : a.1 = 0 := Matrix.ext fun i j => by
      have := hmax (i, j) (Finset.mem_univ _)
      simp only [h0, map_zero, le_zero_iff, map_eq_zero] at this
      exact this
    have := congrFun (congrFun a.mul_inv i0) i0
    rw [hz, zero_mul, Matrix.one_apply_eq] at this
    exact zero_ne_one this
  let k : GL (Fin n) (w.adicCompletion E) := ⟨(a.1 p q)⁻¹ • a.1, a.1 p q • (a⁻¹).1,
    by rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, one_smul, Units.mul_inv],
    by rw [smul_mul_smul_comm, mul_inv_cancel₀ hc, one_smul, Units.inv_mul]⟩
  refine ⟨k, hm.2 ⟨fun i j => ?_, fun i j => ?_⟩, fun g => Units.ext ?_⟩
  · show Valued.v ((a.1 p q)⁻¹ * a.1 i j) ≤ 1
    rw [map_mul, map_inv₀, inv_mul_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 hc))]
    exact hmax (i, j) (Finset.mem_univ _)
  · show a.1 p q * (a⁻¹).1 i j ∈ Ov E w
    rw [mul_comm]; exact hall _ _ _ _
  · show (a⁻¹).1 * g.1 * a.1 = (a.1 p q • (a⁻¹).1) * g.1 * ((a.1 p q)⁻¹ • a.1)
    rw [smul_mul_assoc, smul_mul_smul_comm, mul_inv_cancel₀ hc, one_smul]

end Normaliser

section Component

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain GlobalTheory.HeightCounting
open GlobalTheory.HeckeScalarSph GlobalTheory.SphLabelOps
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem exists_scalar (π : NG.FinTyp L n) (s : SplitPlace L) : ∃ R : GAf L n → Finset (GAf L n),
    (∀ a, TrivOutside {s.v} a → Reps (locK n s.v) a (R a)) ∧ ∀ a, TrivOutside {s.v} a → ∃ c : ℂ, ∀ x ∈ π.S,
      (∀ κ ∈ locK n s.v, NG.rt L n κ x = x) → ∑ γ ∈ R a, rtHom L n ℂ γ x = c • x := by
  classical
  obtain ⟨hdec, hcomm, -⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  choose R hR using exists_repsU (L := L) (n := n) s.v
  refine ⟨R, fun a ha => reps_of_repsU ha (hR a), fun α hα => ?_⟩
  have hRα := reps_of_repsU hα (hR α)
  have hRtriv : ∀ γ ∈ R α, TrivOutside {s.v} γ := fun γ hγ => by
    obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := (hR α).1 γ hγ
    exact triv_mul (triv_mul h₁.2 hα) h₂.2
  let T : (GAf L n → ℂ) →ₗ[ℂ] (GAf L n → ℂ) := ∑ γ ∈ R α, rtHom L n ℂ γ
  have hT : ∀ x, T x = ∑ γ ∈ R α, rtHom L n ℂ γ x := fun x => LinearMap.sum_apply _ _ _
  have conv : ∀ {b x : GAf L n}, (∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ x = k₁ * b * k₂) ↔
      ∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, x = k₁ * b * k₂ :=
    ⟨fun ⟨k₁, h₁, k₂, h₂, t₁, t₂, e⟩ => ⟨k₁, ⟨h₁, t₁⟩, k₂, ⟨h₂, t₂⟩, e⟩,
      fun ⟨k₁, h₁, k₂, h₂, e⟩ => ⟨k₁, h₁.1, k₂, h₂.1, h₁.2, h₂.2, e⟩⟩
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ x ∈ GlobalTheory.SphScalar.fixS (rtHom L n ℂ) π.S (locK n s.v), T x = c • x := by
    refine GlobalTheory.SphScalar.abs_scalar (rtHom L n ℂ) π.S (fun g x hx => π.stable g x hx) π.irr (GlobalTheory.SphScalar.countRank π)
      (locK n s.v) {x | TrivOutside {s.v} x} {y | TrivOutside {s.v}ᶜ y}
      (fun g => by obtain ⟨x, y, hx, hy, e⟩ := hdec g; exact ⟨x, hx, y, hy, e⟩)
      (fun κ hκ b hb => (hcomm κ b hκ.2 hb).eq) R (fun b hb => reps_of_repsU hb (hR b)) T ?_ ?_ ?_
    · intro x hx
      rw [hT]
      refine ⟨π.S.sum_mem fun γ _ => π.stable γ x hx.1, fun κ hκ => ?_⟩
      rw [map_sum]
      have := hRα.sum_eq hRα hκ (fun g => rtHom L n ℂ g x)
        (fun y l hl => by rw [map_mul, Module.End.mul_apply, hx.2 l hl])
      simpa only [map_mul, Module.End.mul_apply] using this
    · intro b hb x _
      rw [hT, hT, map_sum]
      refine Finset.sum_congr rfl fun γ hγ => ?_
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, (hcomm γ b (hRtriv γ hγ) hb).eq]
    · intro b hb x hx
      rw [hT, hT]
      exact GlobalTheory.T.splitPlace_doubleCosetOperators_commute_spherical L n ℂ s α b (R α) (R b) hα hb (fun y hy => (hR α).2 y (conv.1 hy))
        (fun γ hγ => conv.2 ((hR α).1 γ hγ)) (fun y hy => (hR b).2 y (conv.1 hy))
        (fun γ hγ => conv.2 ((hR b).1 γ hγ)) x (fun κ h1 h2 => hx.2 κ ⟨h1, h2⟩)
  exact ⟨c, fun x hx hf => (hT x).symm.trans (hc x ⟨hx, hf⟩)⟩

theorem exists_isLocS (π : NG.FinTyp L n) (s : SplitPlace L) {x : GAf L n → ℂ} (hx : x ∈ π.S) (h0 : x ≠ 0)
    (hK : ∀ κ ∈ locK n s.v, NG.rt L n κ x = x) : ∃ τ, IsLocS π.S s τ := by
  obtain ⟨hdec, hcomm, -⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  obtain ⟨R, hR, hc⟩ := exists_scalar π s
  let Loc : Subgroup (GAf L n) := ⟨⟨⟨{a | TrivOutside {s.v} a}, triv_mul⟩, triv_one⟩, triv_inv⟩
  refine GlobalTheory.RowLocal.isLocS_of_irr π s (Submodule.span ℂ {y | ∃ a ∈ Loc, y = rtHom L n ℂ a x})
    (Submodule.span_le.2 (by rintro _ ⟨a, -, rfl⟩; exact π.stable a x hx)) (fun h => h0 ?_) (fun g hg f hf => ?_)
    fun W' hle hst => irr_of_scalar (rtHom L n ℂ) π.S (fun g x hx => π.stable g x hx) π.irr (locK n s.v) Loc
      (fun κ hκ => hκ.2) {y | TrivOutside {s.v}ᶜ y}
      (fun g => by obtain ⟨x, y, hx, hy, e⟩ := hdec g; exact ⟨x, hx, y, hy, e⟩)
      (fun a ha b hb => (hcomm a b ha hb).eq) R hR hx hK (fun a ha => (hc a ha).imp fun c h => h x hx hK) W' hle hst
  · have : x ∈ Submodule.span ℂ {y | ∃ a ∈ Loc, y = rtHom L n ℂ a x} :=
      Submodule.subset_span ⟨1, one_mem _, by rw [map_one, Module.End.one_apply]⟩
    rwa [h] at this
  · have : (Submodule.span ℂ {y | ∃ a ∈ Loc, y = rtHom L n ℂ a x}).map (rtHom L n ℂ g) ≤
        Submodule.span ℂ {y | ∃ a ∈ Loc, y = rtHom L n ℂ a x} := by
      rw [Submodule.map_span_le]
      rintro _ ⟨a, ha, rfl⟩
      exact Submodule.subset_span ⟨g * a, Loc.mul_mem hg ha, by rw [map_mul, Module.End.mul_apply]⟩
    exact this (Submodule.mem_map_of_mem hf)

theorem under_w (s : SplitPlace L) : s.w.under (𝓞 (maximalRealSubfield L)) = s.v := HeightOneSpectrum.ext s.w_under

theorem eq_complMap (s : SplitPlace L) (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L)
    (hi : Continuous i) (hic : ∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) (y) :
    i y = GlobalTheory.LFun.complMap (under_w s) y := by
  have hd := HeightOneSpectrum.denseRange_algebraMap (K := maximalRealSubfield L) s.v
  refine congrFun (hd.equalizer hi (GlobalTheory.LFun.SplitChart.continuous_complMap (under_w s)) (funext fun y => ?_)) y
  simp only [Function.comp_apply]
  rw [GlobalTheory.LFun.complMap_algebraMap, ← hic, s.i.commutes y]

theorem map_loc_mem_iff (s : SplitPlace L) (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L)
    (hi : Continuous i) (hic : ∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) {x : GAf L n}
    (hx : TrivOutside {s.v} x) :
    Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x) ∈ GlobalTheory.LFun.KGL s.w n ↔ x ∈ Umax L n := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have key : ∀ y, i y ∈ Formalism.UG.Ov L s.w → Valued.v y ≤ 1 := fun y hy =>
      (GlobalTheory.CuspRep.ParLaws.valuation_le_one_iff s.v y).1 (GlobalTheory.SphLoc.le_one_of_map i.toRingHom hi
        ((GlobalTheory.CuspRep.ParLaws.valuation_le_one_iff s.w _).2 hy))
    rw [mem_GLint_iff, ← map_inv, ← map_inv] at h
    exact mem_Umax_of_loc s x hx (fun a b => key _ (h.1 a b)) fun a b => key _ (h.2 a b)
  have key : ∀ y ∈ Umax L n, ∀ a b, (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n y)).1 a b ∈ Formalism.UG.Ov L s.w :=
    fun y hy a b => by
      show i (s.proj (y.1.1 a b)) ∈ _
      rw [eq_complMap s i hi hic]
      exact GlobalTheory.LFun.complMap_mem _ (proj_mem s (hy a b))
  refine mem_GLint_iff.2 ⟨key x h, ?_⟩
  rw [← map_inv, ← map_inv]
  exact key _ (inv_mem h)

theorem isSpherical_of_isLocS (π : NG.FinTyp L n) (s : SplitPlace L)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (hσ : IsLocS π.S s σ) {f : GAf L n → ℂ} (hf : f ∈ π.S)
    (hf0 : f ≠ 0) (hfix : ∀ κ ∈ locK n s.v, NG.rt L n κ f = f) : GlobalTheory.SmGL.IsSpherical σ.ρ := by
  classical
  obtain ⟨i, T₀, hi, hic, -, -, -⟩ := id hσ
  have hI := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  choose lift hlift using fun A => (hI.2.2 A).exists
  have huniq : ∀ A x, TrivOutside {s.v} x → s.loc n x = A → x = lift A := fun A x hx e =>
    (hI.2.2 A).unique ⟨hx, e⟩ (hlift A)
  have hmul : ∀ A B, lift (A * B) = lift A * lift B := fun A B =>
    (huniq _ _ (triv_mul (hlift A).1 (hlift B).1) (by rw [map_mul, (hlift A).2, (hlift B).2])).symm
  have hone : lift 1 = 1 := (huniq _ _ triv_one (map_one _)).symm
  let e : GL (Fin n) (s.w.adicCompletion L) →* GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) :=
    Matrix.GeneralLinearGroup.map i.symm.toRingHom
  have hloc : ∀ g, Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n (lift (e g))) = g := fun g => by
    rw [(hlift _).2]
    exact Units.ext (Matrix.ext fun a b => i.apply_symm_apply _)
  let ρX : Representation ℂ (GL (Fin n) (s.w.adicCompletion L)) (GAf L n → ℂ) :=
    { toFun := fun g => rtHom L n ℂ (lift (e g))
      map_one' := by simp only [map_one, hone]
      map_mul' := fun g h => by simp only [map_mul, hmul] }
  have h1 := GlobalTheory.FinTypSpanLoc.main L n π s σ hσ i hi hic hf
  rw [iSup_subtype', Submodule.mem_iSup_iff_exists_finset] at h1
  obtain ⟨t, ht⟩ := h1
  rw [iSup_subtype'] at ht
  let Tm : {j // j ∈ t} → σ.ρ.IntertwiningMap ρX := fun j =>
    ⟨j.1.1, fun g => LinearMap.ext fun a => by
      have := j.1.2.2 (lift (e g)) (hlift _).1 a
      rw [hloc] at this
      exact this⟩
  refine GlobalTheory.UnrLoc.fixed_ne_bot_of_mem_iSup_range σ.irr Tm (GlobalTheory.SplitWeil.KO _ (Fin n)) ht hf0 fun k hk => ?_
  exact hfix _ ⟨(map_loc_mem_iff s i hi hic (hlift _).1).1
    (by rw [hloc]; exact (GlobalTheory.SmGL.SphCompletion.KO_completion s.w n).le hk), (hlift _).1⟩

open GlobalTheory.StdFrame Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in

theorem compAt_cast {F₁ : Subfield L} (h : F₁ = maximalRealSubfield L) (s : SplitPlace L)
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L)
    (hi : Continuous i) (hic : ∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) (y : AL L) :
    GlobalTheory.LFun.compAt F₁ s.w ((tensCastR h).symm y) = i (s.proj y) := by
  subst h
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | tmul x a =>
    have e : s.proj (x ⊗ₜ[maximalRealSubfield L] a) = s.i x * a s.v := by
      simp only [SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul]
      rfl
    have e2 : ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (h : s.w.under (𝓞 (maximalRealSubfield L)) = v),
        GlobalTheory.LFun.complMap h (a v) = GlobalTheory.AdeleBaseChange.locMap _ s.w (a (s.w.under (𝓞 (maximalRealSubfield L)))) := by
      rintro _ rfl; rfl
    rw [e, map_mul, hic, eq_complMap s i hi hic, e2, mul_comm]
    rfl

open GlobalTheory.StdFrame Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in

theorem triv_cast {F₁ : Subfield L} (h : F₁ = maximalRealSubfield L) (s : SplitPlace L) (x : GAf L n) :
    TrivOutside {s.v} x ↔ ∀ u, u ≠ s.w.under (𝓞 F₁) → ((x.1.1.map (tensCastR h).symm).map
      (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F₁ u) (AlgHom.id F₁ L))) = 1 := by
  subst h
  rw [under_w]
  refine forall_congr' fun u => imp_congr (by simp) ?_
  let c := (Algebra.TensorProduct.comm (maximalRealSubfield L) L (u.adicCompletion (maximalRealSubfield L))).toRingEquiv
  have e : ∀ y : AL L, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV (maximalRealSubfield L) u) (AlgHom.id _ L)
      ((tensCastR rfl).symm y) = c (compAt L u y) := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul x a => rfl
  have e' : (x.1.1.map (tensCastR rfl).symm).map (Algebra.TensorProduct.map
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV (maximalRealSubfield L) u) (AlgHom.id _ L)) = (x.1.1.map (compAt L u)).map c :=
    Matrix.ext fun a b => e _
  rw [e']
  refine ⟨fun h => by rw [h, Matrix.map_one _ (map_zero _) (map_one _)], fun h => Matrix.map_injective c.injective ?_⟩
  exact h.trans (Matrix.map_one _ (map_zero _) (map_one _)).symm

end Component

section Conj

variable {R S : Type} [CommRing R] [CommRing S] {m n : ℕ} (φ : R →+* S) {β : Matrix (Fin m) (Fin n) R} {β' : Matrix (Fin n) (Fin m) R}

theorem map_mul_eq_one (h : β * β' = 1) : β.map φ * β'.map φ = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]

theorem map_conj (M : Matrix (Fin n) (Fin n) R) : (β * M * β').map φ = β.map φ * M.map φ * β'.map φ := by
  rw [Matrix.map_mul, Matrix.map_mul]

theorem map_conj_eq_one_iff (h1 : β * β' = 1) (h2 : β' * β = 1) (M : Matrix (Fin n) (Fin n) R) :
    M.map φ = 1 ↔ (β * M * β').map φ = 1 := by
  have m1 := map_mul_eq_one φ h1
  have m2 := map_mul_eq_one φ h2
  rw [map_conj]
  refine ⟨fun h => by rw [h, Matrix.mul_one, m1], fun e' => ?_⟩
  calc M.map φ = (β'.map φ * β.map φ) * M.map φ * (β'.map φ * β.map φ) := by rw [m2, Matrix.one_mul, Matrix.mul_one]
    _ = β'.map φ * (β.map φ * M.map φ * β'.map φ) * β.map φ := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [e', Matrix.mul_one, m2]

end Conj

end GlobalTheory.TwInputs.Eig

end
