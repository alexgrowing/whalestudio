import Mathlib
import Development.AutomorphicArithmetic.DivisorFrames.FunctionFieldEssFiniteTypeInt
import Development.AutomorphicArithmetic.DivisorFrames.ExistsComplexEmbeddingExtension
import Development.AutomorphicArithmetic.DivisorFrames.EqGenericPointOfIntegralDim
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ChiLenPicPushforwardOfIsClosedImmersion
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ConsGeo

private theorem spC {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

private theorem spInj {A B : Type} [CommRing A] [CommRing B] (f g : A →+* B) (h : spMap f = spMap g) : f = g := by
  have h1 : CommRingCat.ofHom f = CommRingCat.ofHom g := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom h1

private theorem gptInj (X : Scheme.{0}) [IsIntegral X] {k : Type} [Field k] (j j' : X.functionField →+* k)
    (h : spMap j ≫ gpt X = spMap j' ≫ gpt X) : j = j' := by
  haveI : Mono (gpt X) := inferInstanceAs (Mono (X.fromSpecStalk (genericPoint X)))
  exact spInj _ _ ((cancel_mono _).1 h)

private theorem factorRes (X : Scheme.{0}) {k : Type} [Field k] (w : Sp k ⟶ X) :
    ∃ ψ : X.residueField (w (closedPoint k)) →+* k, w = spMap ψ ≫ X.fromSpecResidueField _ :=
  ⟨(X.descResidueField (Scheme.stalkClosedPointTo w)).hom,
    (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k X w).symm⟩

private theorem factorGen (X : Scheme.{0}) [IsIntegral X] {k : Type} [Field k] (w : Sp k ⟶ X)
    (h : w (closedPoint k) = genericPoint X) : ∃ θ : X.functionField →+* k, w = spMap θ ≫ gpt X := by
  obtain ⟨ψ, hψ⟩ := factorRes X w
  have key : ∀ x : X, x = genericPoint X → ∀ ψ : X.residueField x →+* k,
      ∃ θ : X.functionField →+* k, spMap ψ ≫ X.fromSpecResidueField x = spMap θ ≫ gpt X := by
    rintro _ rfl ψ
    refine ⟨ψ.comp (X.residue (genericPoint X)).hom, ?_⟩
    rw [spC, Category.assoc]
    rfl
  obtain ⟨θ, hθ⟩ := key _ h ψ
  exact ⟨θ, hψ.trans hθ⟩

private theorem ptComp {X : Scheme.{0}} {k k' : Type} [Field k] [Field k'] (j : k →+* k') (w : Sp k ⟶ X) :
    (spMap j ≫ w) (closedPoint k') = w (closedPoint k) := by
  exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg w (Subsingleton.elim (α := PrimeSpectrum k) _ _))

private theorem gptPt (X : Scheme.{0}) [IsIntegral X] : gpt X (closedPoint X.functionField) = genericPoint X :=
  Scheme.fromSpecStalk_closedPoint

private theorem exJ (k₀ : Type) [Field k₀] [NumberField k₀] (σ : k₀ →+* ℂ) (X : Scheme.{0}) [IsIntegral X]
    (s : X ⟶ Sp k₀) [LocallyOfFiniteType s] :
    ∃ j : X.functionField →+* ℂ, spMap j ≫ gpt X ≫ s = spMap σ := by
  obtain ⟨j, hj⟩ := UpperTheory.exists_complex_embedding_extension k₀ X.functionField (Spec.preimage (gpt X ≫ s)).hom σ (UpperTheory.functionField_essFiniteType_int k₀ X s)
  refine ⟨j, ?_⟩
  rw [← hj, spC]
  congr 1
  exact (Spec.map_preimage (gpt X ≫ s)).symm

private theorem integralOfFinite {F K : Type} [Field F] [Field K] (ψ : F →+* K) (j : K →+* ℂ)
    (h : Finite {j' : K →+* ℂ // j'.comp ψ = j.comp ψ}) : ψ.IsIntegral := by
  letI := ψ.toAlgebra
  letI := j.toAlgebra
  have halg : Algebra.IsAlgebraic F K := by
    by_contra hn
    haveI : Algebra.Transcendental F K := Algebra.transcendental_iff_not_isAlgebraic.2 hn
    haveI := Field.infinite_emb_of_transcendental F K
    let l : AlgebraicClosure K →ₐ[K] ℂ := IsAlgClosed.lift
    let f : Field.Emb F K → {j' : K →+* ℂ // j'.comp ψ = j.comp ψ} := fun e =>
      ⟨l.toRingHom.comp (AlgHom.toRingHom e), by
        ext x
        have h1 : (e : K →ₐ[F] AlgebraicClosure K) (ψ x) = algebraMap K (AlgebraicClosure K) (ψ x) :=
          (AlgHom.commutes (e : K →ₐ[F] AlgebraicClosure K) x).trans
            (IsScalarTower.algebraMap_apply F K (AlgebraicClosure K) x)
        change l ((e : K →ₐ[F] AlgebraicClosure K) (ψ x)) = j (ψ x)
        rw [h1, l.commutes]; rfl⟩
    have hf : Function.Injective f := by
      intro e e' he
      apply AlgHom.ext
      intro x
      have := congrArg (fun t : {j' : K →+* ℂ // j'.comp ψ = j.comp ψ} => t.1 x) he
      exact l.toRingHom.injective this
    exact not_finite_iff_infinite.2 (Infinite.of_injective f hf) h
  exact (Algebra.IsAlgebraic.isIntegral (K := F) (A := K)).isIntegral

private theorem cardEmb {F K : Type} [Field F] [Field K] (θ : F →+* K) (hθ : θ.IsIntegral) (j₀ : F →+* ℂ) :
    Nat.card {j : K →+* ℂ // j.comp θ = j₀} = embDeg θ := by
  letI := θ.toAlgebra
  letI := j₀.toAlgebra
  haveI : CharZero F := RingHom.charZero j₀
  haveI : Algebra.IsIntegral F K := ⟨hθ⟩
  haveI : Algebra.IsSeparable F K := inferInstance
  unfold embDeg
  rw [← Field.finSepDegree_eq_finrank_of_isSeparable, Field.finSepDegree_eq_of_isAlgClosed F K ℂ]
  refine Nat.card_congr ⟨fun j => ⟨j.1, fun x => DFunLike.congr_fun j.2 x⟩,
    fun e => ⟨e.toRingHom, RingHom.ext fun x => e.commutes x⟩, fun _ => rfl, fun _ => rfl⟩

theorem UpperTheory.degree_matching_families :
    ∀ (k₀ : Type) [Field k₀] [NumberField k₀] (σ : k₀ →+* ℂ) (ι κ : Type) [Fintype ι] [DecidableEq κ] (X : ι → Scheme.{0}) (Y : κ → Scheme.{0}) [∀ a, IsIntegral (X a)] [∀ b, IsIntegral (Y b)] (sX : ∀ a, X a ⟶ Sp k₀) (sY : ∀ b, Y b ⟶ Sp k₀) [∀ a, LocallyOfFiniteType (sX a)] [∀ b, LocallyOfFiniteType (sY b)] (d n : ℕ) (P : ∀ a, Set (X a)) (Q : ∀ b, Set (Y b)) (M : ∀ (k : Type) [Field k] (a : ι) (b : κ), (Sp k ⟶ X a) → (Sp k ⟶ Y b) → Prop), (∀ a, topologicalKrullDim (X a) = d) → (∀ b, topologicalKrullDim (Y b) = d) → 0 < n → (∀ a, genericPoint (X a) ∈ P a) → (∀ b, genericPoint (Y b) ∈ Q b) → (∀ (k : Type) [Field k] a b w q, M k a b w q → w ≫ sX a = q ≫ sY b ∧ w (closedPoint k) ∈ P a ∧ q (closedPoint k) ∈ Q b) → (∀ (k : Type) [Field k] a (w : Sp k ⟶ X a), w (closedPoint k) ∈ P a → ∃ b q, M k a b w q) → (∀ (k : Type) [Field k] a b b' w q q', M k a b w q → M k a b' w q' → (⟨b, q⟩ : Σ b, (Sp k ⟶ Y b)) = ⟨b', q'⟩) → (∀ (k k' : Type) [Field k] [Field k'] (ψ : k →+* k') a b w q, M k a b w q → M k' a b (spMap ψ ≫ w) (spMap ψ ≫ q)) → (∀ b (q : Sp ℂ ⟶ Y b), q ≫ sY b = spMap σ → q (closedPoint ℂ) ∈ Q b → Nat.card {w : Σ a, (Sp ℂ ⟶ X a) // M ℂ w.1 b w.2 q} = n) → ∃ (b : ι → κ) (θ : ∀ a, (Y (b a)).functionField →+* (X a).functionField), (∀ a, M _ a (b a) (gpt (X a)) (spMap (θ a) ≫ gpt (Y (b a)))) ∧ (∀ a, 0 < embDeg (θ a)) ∧ ∀ b₀, ∑ a ∈ Finset.univ.filter (fun a => b a = b₀), embDeg (θ a) = n := by
  intro k₀ _ _ σ ι κ _ _ X Y _ _ sX sY _ _ d n P Q M hdX hdY hn hP hQ hM hex huniq hbc hcard
  classical
  have fin : ∀ a b (F : Type) [Field F] (φ : F →+* (X a).functionField) (g : Sp F ⟶ Y b),
      M _ a b (gpt (X a)) (spMap φ ≫ g) →
      ∃ j : (X a).functionField →+* ℂ, Finite {j' : (X a).functionField →+* ℂ // j'.comp φ = j.comp φ} := by
    intro a b F _ φ g h
    obtain ⟨j, hj⟩ := exJ k₀ σ (X a) (sX a)
    refine ⟨j, ?_⟩
    have h1 := hbc _ _ j _ _ _ _ h
    obtain ⟨e1, -, e3⟩ := hM _ _ _ _ _ h1
    have h2 := hcard b (spMap j ≫ spMap φ ≫ g) (by rw [← e1, Category.assoc, hj]) e3
    haveI := Nat.finite_of_card_ne_zero (h2.trans_ne hn.ne')
    let f : {j' : (X a).functionField →+* ℂ // j'.comp φ = j.comp φ} →
        {w : Σ a, (Sp ℂ ⟶ X a) // M ℂ w.1 b w.2 (spMap j ≫ spMap φ ≫ g)} := fun j' =>
      ⟨⟨a, spMap j'.1 ≫ gpt (X a)⟩, by
        have h3 := hbc _ _ j'.1 _ _ _ _ h
        rwa [← Category.assoc, ← spC, j'.2, spC, Category.assoc] at h3⟩
    refine Finite.of_injective f ?_
    intro j₁ j₂ he
    have h4 : (⟨a, spMap j₁.1 ≫ gpt (X a)⟩ : Σ a, (Sp ℂ ⟶ X a)) = ⟨a, spMap j₂.1 ≫ gpt (X a)⟩ :=
      congrArg Subtype.val he
    exact Subtype.ext (gptInj _ _ _ (eq_of_heq (Sigma.mk.inj h4).2))
  have step1 : ∀ a, ∃ (b : κ) (θ : (Y b).functionField →+* (X a).functionField),
      M _ a b (gpt (X a)) (spMap θ ≫ gpt (Y b)) := by
    intro a
    obtain ⟨b, q, hq⟩ := hex _ a (gpt (X a)) (by rw [gptPt]; exact hP a)
    obtain ⟨ψ, hψ⟩ := factorRes (Y b) q
    obtain ⟨j, hj⟩ := fin a b _ ψ _ (hψ ▸ hq)
    have hint := integralOfFinite ψ j hj
    have hgen := UpperTheory.eq_genericPoint_of_integral_dim k₀ (Y b) (X a) (sY b) (sX a) d (hdY b) (hdX a) _ _ ψ (RingHom.id _) hint (by
      rw [← Category.assoc, ← hψ, ← (hM _ _ _ _ _ hq).1]
      simp [spMap])
    obtain ⟨θ, hθ⟩ := factorGen (Y b) q hgen
    exact ⟨b, θ, hθ ▸ hq⟩
  choose b θ hθ using step1
  have hint : ∀ a, (θ a).IsIntegral := fun a => by
    obtain ⟨j, hj⟩ := fin a (b a) _ (θ a) _ (hθ a)
    exact integralOfFinite _ j hj
  refine ⟨b, θ, hθ, fun a => ?_, fun b₀ => ?_⟩
  · obtain ⟨j, hj⟩ := fin a (b a) _ (θ a) _ (hθ a)
    rw [← cardEmb (θ a) (hint a) (j.comp (θ a))]
    haveI : Nonempty {j' : (X a).functionField →+* ℂ // j'.comp (θ a) = j.comp (θ a)} := ⟨⟨j, rfl⟩⟩
    exact Nat.card_pos
  · obtain ⟨j₀, hj₀⟩ := exJ k₀ σ (Y b₀) (sY b₀)
    have hc := hcard b₀ (spMap j₀ ≫ gpt (Y b₀)) (by rw [Category.assoc, hj₀])
      (by rw [ptComp, gptPt]; exact hQ b₀)
    haveI := Nat.finite_of_card_ne_zero (hc.trans_ne hn.ne')
    have hfib : ∀ a, Nat.card {w : Sp ℂ ⟶ X a // M ℂ a b₀ w (spMap j₀ ≫ gpt (Y b₀))} =
        if b a = b₀ then embDeg (θ a) else 0 := by
      intro a
      have hgen : ∀ w : Sp ℂ ⟶ X a, M ℂ a b₀ w (spMap j₀ ≫ gpt (Y b₀)) →
          ∃ j : (X a).functionField →+* ℂ, w = spMap j ≫ gpt (X a) ∧
            (⟨b a, spMap j ≫ spMap (θ a) ≫ gpt (Y (b a))⟩ : Σ b, (Sp ℂ ⟶ Y b)) = ⟨b₀, spMap j₀ ≫ gpt (Y b₀)⟩ := by
        intro w hw
        obtain ⟨ψ, hψ⟩ := factorRes (X a) w
        obtain ⟨b', q', hq'⟩ := hex ((X a).residueField (w (closedPoint ℂ))) a ((X a).fromSpecResidueField _)
          (by
            have := (hM _ _ _ _ _ hw).2.1
            exact (Scheme.fromSpecResidueField_apply (w (closedPoint ℂ)) _).symm ▸ this)
        have h1 := hbc _ _ ψ _ _ _ _ hq'
        rw [← hψ] at h1
        have h2 := huniq _ _ _ _ _ _ _ h1 hw
        obtain ⟨rfl, h3⟩ := Sigma.mk.inj h2
        have h4 := eq_of_heq h3
        have h5 : q' (closedPoint _) = genericPoint (Y b') := by
          rw [← ptComp ψ q', h4, ptComp, gptPt]
        obtain ⟨θ', hθ'⟩ := factorGen (Y b') q' h5
        have h6 := UpperTheory.eq_genericPoint_of_integral_dim k₀ (X a) (Y b') (sX a) (sY b') d (hdX a) (hdY b') _ _ (RingHom.id _) θ'
          (RingHom.isIntegral_of_surjective _ Function.surjective_id) (by
            rw [(hM _ _ _ _ _ hq').1, ← Category.assoc _ (gpt _), ← hθ']
            simp [spMap])
        obtain ⟨j, hj⟩ := factorGen (X a) w h6
        refine ⟨j, hj, ?_⟩
        have h7 := hbc _ _ j _ _ _ _ (hθ a)
        rw [← hj] at h7
        exact huniq _ _ _ _ _ _ _ h7 hw
      split_ifs with hb
      · subst hb
        rw [← cardEmb (θ a) (hint a) j₀]
        symm
        let f : {j : (X a).functionField →+* ℂ // j.comp (θ a) = j₀} →
            {w : Sp ℂ ⟶ X a // M ℂ a (b a) w (spMap j₀ ≫ gpt (Y (b a)))} := fun j =>
          ⟨spMap j.1 ≫ gpt (X a), by
            have h3 := hbc _ _ j.1 _ _ _ _ (hθ a)
            rwa [← Category.assoc, ← spC, j.2] at h3⟩
        refine Nat.card_eq_of_bijective f ⟨fun j₁ j₂ he => ?_, fun w => ?_⟩
        · exact Subtype.ext (gptInj _ _ _ (congrArg Subtype.val he))
        · obtain ⟨j, hj, h⟩ := hgen w.1 w.2
          have h1 := eq_of_heq (Sigma.mk.inj h).2
          rw [← Category.assoc, ← spC] at h1
          exact ⟨⟨j, gptInj _ _ _ h1⟩, Subtype.ext hj.symm⟩
      · haveI : IsEmpty {w : Sp ℂ ⟶ X a // M ℂ a b₀ w (spMap j₀ ≫ gpt (Y b₀))} := ⟨fun w => by
          obtain ⟨j, -, h⟩ := hgen w.1 w.2
          exact hb (Sigma.mk.inj h).1⟩
        exact Nat.card_of_isEmpty
    let e : {w : Σ a, (Sp ℂ ⟶ X a) // M ℂ w.1 b₀ w.2 (spMap j₀ ≫ gpt (Y b₀))} ≃
        Σ a, {w : Sp ℂ ⟶ X a // M ℂ a b₀ w (spMap j₀ ≫ gpt (Y b₀))} :=
      ⟨fun w => ⟨w.1.1, w.1.2, w.2⟩, fun w => ⟨⟨w.1, w.2.1⟩, w.2.2⟩, fun _ => rfl, fun _ => rfl⟩
    haveI := Finite.of_equiv _ e
    haveI : ∀ a, Finite {w : Sp ℂ ⟶ X a // M ℂ a b₀ w (spMap j₀ ≫ gpt (Y b₀))} := fun a =>
      Finite.of_injective (β := Σ a, {w : Sp ℂ ⟶ X a // M ℂ a b₀ w (spMap j₀ ≫ gpt (Y b₀))})
        (fun w => ⟨a, w⟩) (fun _ _ h => eq_of_heq (Sigma.mk.inj h).2)
    rw [← hc, Nat.card_congr e, Nat.card_sigma, Finset.sum_filter]
    exact Finset.sum_congr rfl fun a _ => (hfib a).symm
