import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetDecoSetLatticeReps

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.DecoClassCount

open scoped TensorProduct in

theorem exists_span_quot {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] :
    ∃ v : Fin (Module.finrank R N) → N ⧸ (I • ⊤ : Submodule R N),
      Submodule.span R (Set.range v) = ⊤ := by
  have : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N) (Module.finrank R N)
    (fun P => by
      have := P.isMaximal
      let : Field ((R ⧸ I) ⧸ P.asIdeal) := Ideal.Quotient.field _
      rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal)
        ((R ⧸ I) ⧸ P.asIdeal) N).finrank_eq]
      have h1 := Module.rankAtStalk_baseChange (R := R) (M := N) (S := (R ⧸ I) ⧸ P.asIdeal) ⊥
      rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
      exact h1)
  refine ⟨(TensorProduct.quotTensorEquivQuotSMul N I) ∘ b, ?_⟩
  have h1 : Submodule.span R (Set.range b) = ⊤ := by
    rw [← Submodule.restrictScalars_span R (R ⧸ I) Ideal.Quotient.mk_surjective, b.span_eq,
      Submodule.restrictScalars_top]
  have h2 := congrArg (Submodule.map (TensorProduct.quotTensorEquivQuotSMul N I).toLinearMap) h1
  rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h2
  rw [Set.range_comp]
  exact h2

theorem exists_determining {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] :
    ∃ v : Fin (Module.finrank R N) → N, ∀ f g : N →ₗ[R] R ⧸ I, (∀ i, f (v i) = g (v i)) → f = g := by
  obtain ⟨v, hv⟩ := exists_span_quot (R := R) (N := N) I
  choose u hu using fun i => Submodule.Quotient.mk_surjective _ (v i)
  have hk : ∀ f : N →ₗ[R] R ⧸ I, (I • ⊤ : Submodule R N) ≤ LinearMap.ker f := by
    intro f
    refine Submodule.smul_le.2 fun a ha x _ => ?_
    rw [LinearMap.mem_ker, map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_mul]
  refine ⟨u, fun f g hfg => ?_⟩
  have : Submodule.liftQ _ f (hk f) = Submodule.liftQ _ g (hk g) :=
    LinearMap.ext_on_range hv fun i => by
      rw [← hu i]
      exact hfg i
  ext x
  simpa using LinearMap.congr_fun this (Submodule.Quotient.mk x)

theorem finrank_of_span_top {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (p : Submodule (𝓞 K) V)
    (h : Submodule.span K (p : Set V) = ⊤) : Module.finrank (𝓞 K) p = Module.finrank K V := by
  have : IsLocalizedModule (nonZeroDivisors (𝓞 K)) p.subtype := by
    refine ⟨fun s => ?_, fun y => ?_, fun {a b} hab => ⟨1, by simpa using hab⟩⟩
    · have := isLocalizedModule_id (nonZeroDivisors (𝓞 K)) V K
      exact IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 K)) (LinearMap.id : V →ₗ[𝓞 K] V) s
    · have hy : y ∈ Submodule.span K (p : Set V) := h ▸ Submodule.mem_top
      obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ y hy
      rw [Submodule.span_eq] at ht
      exact ⟨(⟨_, ht⟩, t), rfl⟩
  rw [← IsLocalizedModule.finrank_eq (nonZeroDivisors (𝓞 K)) p.subtype le_rfl,
    IsFractionRing.finrank_right_eq (𝓞 K) K V]

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

def IsLocForm (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n))
    (φ : Sp E n → 𝓞 E ⧸ P.asIdeal) : Prop :=
  (∀ x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N, ∀ y ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N, φ (x + y) = φ x + φ y) ∧
  ∀ (a : 𝓞 E), ∀ x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N, φ (a • x) = Ideal.Quotient.mk P.asIdeal a * φ x

omit [StarRing E] in

theorem exists_determining_lattice (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n))
    (hN : Submodule.IsLattice E N) :
    ∃ v : Fin n → Sp E n, ∀ φ ψ, IsLocForm P N φ → IsLocForm P N ψ → (∀ i, φ (v i) = ψ (v i)) →
      ∀ x ∈ N, φ x = ψ x := by
  have : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 (Submodule.IsLattice.fg (self := hN))
  have : Module.FinitePresentation (𝓞 E) N := Module.finitePresentation_of_finite _ _
  have : Module.Flat (𝓞 E) N := inferInstance
  have : Module.Projective (𝓞 E) N := Module.Flat.projective_of_finitePresentation
  have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  have hr : Module.finrank (𝓞 E) N = n := by
    simpa using finrank_of_span_top N hN.span_eq_top
  obtain ⟨v, hv⟩ := exists_determining (R := 𝓞 E) (N := N) P.asIdeal
  have hle : N ≤ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N := fun x hx =>
    ⟨1, P.asIdeal.primeCompl.one_mem, by simpa using hx⟩
  let lin : ∀ φ, IsLocForm P N φ → (N →ₗ[𝓞 E] 𝓞 E ⧸ P.asIdeal) := fun φ hφ =>
    { toFun := fun x => φ x
      map_add' := fun x y => hφ.1 x (hle x.2) y (hle y.2)
      map_smul' := fun a x => hφ.2 a x (hle x.2) }
  refine ⟨fun i => v (Fin.cast hr.symm i), fun φ ψ hφ hψ h x hx => ?_⟩
  have := hv (lin φ hφ) (lin ψ hψ) fun i => h (Fin.cast hr i)
  exact LinearMap.congr_fun this ⟨x, hx⟩

theorem card_fibre_le (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E n)) :
    {d : DecoSet E n ST SG | d.1.N = N}.Finite ∧ {d : DecoSet E n ST SG | d.1.N = N}.ncard ≤
      (∏ P ∈ ST, Ideal.absNorm P.asIdeal ^ n) * ∏ w ∈ SG, Ideal.absNorm w.asIdeal ^ (n ^ 2) := by
  classical
  rcases Set.eq_empty_or_nonempty {d : DecoSet E n ST SG | d.1.N = N} with he | ⟨d0, hd0⟩
  · rw [he]; simp
  have hlat : Submodule.IsLattice E N := by
    have := d0.2.lat
    rwa [show d0.1.N = N from hd0] at this
  choose v hv using fun P => exists_determining_lattice P N hlat
  haveI hfin : ∀ P : HeightOneSpectrum (𝓞 E), Finite (𝓞 E ⧸ P.asIdeal) := fun P =>
    Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  let Φ : DecoSet E n ST SG →
      (∀ P : ST, Fin n → 𝓞 E ⧸ P.1.asIdeal) × (∀ w : SG, Fin n → Fin n → 𝓞 E ⧸ w.1.asIdeal) :=
    fun d => (fun P i => d.1.f P (v P.1 i), fun w i => d.1.be w (v w.1 i))
  have hinj : Set.InjOn Φ {d : DecoSet E n ST SG | d.1.N = N} := by
    intro d hd d' hd' hdd
    replace hd : d.1.N = N := hd
    replace hd' : d'.1.N = N := hd'
    have hf : ∀ e : DecoSet E n ST SG, e.1.N = N → ∀ P : ST, IsLocForm P.1 N (e.1.f P) := by
      rintro e rfl P
      exact ⟨e.2.f_add P, e.2.f_smul P⟩
    have hb : ∀ e : DecoSet E n ST SG, e.1.N = N → ∀ (w : SG) (j : Fin n),
        IsLocForm w.1 N fun x => e.1.be w x j := by
      rintro e rfl w j
      exact ⟨fun x hx y hy => congrFun (e.2.be_add w x hx y hy) j,
        fun a x hx => congrFun (e.2.be_smul w a x hx) j⟩
    apply Subtype.ext
    refine d.2.ext_on d'.2 (hd.trans hd'.symm) (fun P x hx => ?_) (fun w x hx => ?_)
    · exact hv P.1 _ _ (hf d hd P) (hf d' hd' P)
        (fun i => congrFun (congrFun (congrArg Prod.fst hdd) P) i) x (hd ▸ hx)
    · funext j
      exact hv w.1 _ _ (hb d hd w j) (hb d' hd' w j)
        (fun i => congrFun (congrFun (congrFun (congrArg Prod.snd hdd) w) i) j) x (hd ▸ hx)
  refine ⟨Set.Finite.of_finite_image (Set.toFinite _) hinj, ?_⟩
  have hle := Set.ncard_le_ncard_of_injOn Φ (t := Set.univ) (fun _ _ => Set.mem_univ _) hinj
    (Set.toFinite _)
  refine hle.trans (le_of_eq ?_)
  have hc : ∀ P : HeightOneSpectrum (𝓞 E), Nat.card (𝓞 E ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal :=
    fun P => by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [Set.ncard_univ, Nat.card_prod, Nat.card_pi, Nat.card_pi]
  simp only [Nat.card_fun, hc, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul, ← sq]
  rw [Finset.prod_coe_sort ST (fun P => Ideal.absNorm P.asIdeal ^ n),
    Finset.prod_coe_sort SG (fun P => Ideal.absNorm P.asIdeal ^ (n ^ 2))]

theorem card_classes_le : ∀ (X : Fields), X.Ok → ∀ (n : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 X.E))), Finite (MulAction.orbitRel.Quotient ((⊤ : Subgroup (UF X.E n)).prod (⊥ : Subgroup (GLG X.E n SG))) (DecoSet X.E n ST SG)) ∧ (Nat.card (MulAction.orbitRel.Quotient ((⊤ : Subgroup (UF X.E n)).prod (⊥ : Subgroup (GLG X.E n SG))) (DecoSet X.E n ST SG)) : ℝ) ≤ (3 * ((Module.finrank ℚ X.E : ℝ) ^ 2 * (n : ℝ) ^ 4 * (|(discr X.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ X.E : ℝ))) ^ 2)) ^ (3 * Module.finrank ℚ X.E * n ^ 2) * (∏ P ∈ ST, (Ideal.absNorm P.asIdeal : ℝ) ^ n) * ∏ w ∈ SG, (Ideal.absNorm w.asIdeal : ℝ) ^ (n ^ 2) := by
  intro X hX n ST SG
  classical
  have hΓ : ∀ g : UF X.E n, (g, (1 : GLG X.E n SG)) ∈
      (⊤ : Subgroup (UF X.E n)).prod (⊥ : Subgroup (GLG X.E n SG)) := fun g =>
    ⟨Subgroup.mem_top _, Subgroup.one_mem _⟩
  refine ⟨DecoSet.finite_orbits (posStar_of_conj hX.conjE) _ hΓ, ?_⟩
  have := hX.realF
  have := hX.cplxE
  have : Algebra.IsQuadraticExtension X.F X.E := ⟨hX.rankE⟩
  have : IsCMField X.E := IsCMField.ofCMExtension X.F X.E
  have hs : ∀ x : X.E, star x = IsCMField.complexConj X.E x := by
    intro x
    let φ : X.E →+* ℂ := (IsAlgClosed.lift : X.E →ₐ[ℚ] ℂ).toRingHom
    apply φ.injective
    rw [hX.conjE, IsCMField.complexEmbedding_complexConj]
  obtain ⟨Rs, hR, H⟩ := GlobalTheory.exists_finset_decoSet_lattice_reps X.E hs n
  let fib : Submodule (𝓞 X.E) (Sp X.E n) → Finset (DecoSet X.E n ST SG) := fun N =>
    (card_fibre_le ST SG N).1.toFinset
  let B : ℕ := (∏ P ∈ ST, Ideal.absNorm P.asIdeal ^ n) * ∏ w ∈ SG, Ideal.absNorm w.asIdeal ^ (n ^ 2)
  have hfib : ∀ N, (fib N).card ≤ B := fun N => by
    rw [← Set.ncard_eq_toFinset_card _ (card_fibre_le ST SG N).1]
    exact (card_fibre_le ST SG N).2
  have hS : (Rs.biUnion fib).card ≤ Rs.card * B := Finset.card_biUnion_le_card_mul _ _ _ fun N _ => hfib N
  have hsurj : Function.Surjective (fun d : ↥(Rs.biUnion fib) => (Quotient.mk'' d.1 :
      MulAction.orbitRel.Quotient ((⊤ : Subgroup (UF X.E n)).prod (⊥ : Subgroup (GLG X.E n SG)))
        (DecoSet X.E n ST SG))) := by
    intro c
    induction c using Quotient.inductionOn' with
    | h d =>
      obtain ⟨g, hg⟩ := H ST SG d
      refine ⟨⟨(g, (1 : GLG X.E n SG)) • d, Finset.mem_biUnion.2 ⟨_, hg, ?_⟩⟩, ?_⟩
      · exact (Set.Finite.mem_toFinset _).2 rfl
      · apply Quotient.sound'
        rw [MulAction.orbitRel_apply]
        exact ⟨⟨(g, 1), hΓ g⟩, rfl⟩
  have h1 := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_eq_fintype_card (α := ↥(Rs.biUnion fib)), Fintype.card_coe] at h1
  have h2 : ((Rs.card * B : ℕ) : ℝ) = Rs.card * (∏ P ∈ ST, (Ideal.absNorm P.asIdeal : ℝ) ^ n) *
      ∏ w ∈ SG, (Ideal.absNorm w.asIdeal : ℝ) ^ (n ^ 2) := by
    simp only [B]
    push_cast
    ring
  refine (Nat.cast_le.2 (h1.trans hS)).trans (h2.le.trans ?_)
  gcongr

end GlobalTheory.DecoClassCount
