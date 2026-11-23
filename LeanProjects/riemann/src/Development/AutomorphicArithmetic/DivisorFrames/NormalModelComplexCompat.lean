import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AutomorphicArithmetic.LocalEmbeddings.ValCount
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AutomorphicArithmetic.DivisorFrames.ValuationNormSumExtensions
import Development.AutomorphicArithmetic.DivisorFrames.PlaceDegreeResidueFormula
import Development.AutomorphicArithmetic.DivisorFrames.ValuationSubringUniqueOfPrime
import Development.AutomorphicArithmetic.DivisorFrames.ExistsApproximationValuations
import Development.AutomorphicArithmetic.DivisorFrames.EmbeddingCountExtensions
import Development.AutomorphicArithmetic.DivisorFrames.CountableFunctionFieldFiniteType
import Development.AutomorphicArithmetic.DivisorFrames.OrderEqValuationCodimOne
import Development.AutomorphicArithmetic.DivisorFrames.OrderCodimOneFiniteMap
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp GlobalTheory.ValCount
open scoped Classical

private theorem ne_top_of_dvr {L : Type} [Field L] (V : ValuationSubring L) [IsDiscreteValuationRing V] : V ≠ ⊤ := by
  rintro rfl
  exact IsDiscreteValuationRing.not_isField (⊤ : ValuationSubring L)
    (MulEquiv.isField (Field.toIsField L) Subring.topEquiv.toMulEquiv)

private theorem one_term {F F' K L : Type} [Field F] [CharZero F] [Field F'] [Field K] [Field L] (ε : F →+* F')
    (k : F →+* K) (φ : K →+* L) (c : F' →+* L) (hc : φ.comp k = c.comp ε) (O : ValuationSubring F')
    [IsDiscreteValuationRing O] (W : ValuationSubring K) [IsDiscreteValuationRing W]
    (hW : W.comap k = O.comap ε) (hD : ∀ V : ValuationSubring F', V.comap ε = O.comap ε → IsDiscreteValuationRing V)
    (hD' : ∀ V : ValuationSubring L, V.comap φ = W → IsDiscreteValuationRing V)
    {π : F'} (hπ : π ≠ 0) (hπ' : ∀ V : ValuationSubring F', V.comap ε = O.comap ε → V ≠ O → π ∈ V ∧ π⁻¹ ∈ V)
    {p : ℕ} (hp : p ≠ 0) {a : K} (ha : a ≠ 0) (V : ValuationSubring L) :
    (if V.comap φ = W ∧ ∀ o : O, c o ∈ V then vord V (φ a) * (vdeg φ V : ℤ) else 0) * (vord O π * vord W p) =
      (if V.comap φ = W then vord V (c π) * (vdeg φ V : ℤ) else 0) * (vord O p * vord W a) := by
  by_cases h1 : V.comap φ = W
  swap
  · simp [h1]
  have h2 : (V.comap c).comap ε = O.comap ε := by
    rw [ValuationSubring.comap_comap, ← hc, ← ValuationSubring.comap_comap, h1, hW]
  have := hD _ h2
  have := hD' _ h1
  by_cases h3 : ∀ o : O, c o ∈ V
  · have h4 : O = V.comap c :=
      ValuationSubring.eq_of_le_of_ne_top O (fun x hx => h3 ⟨x, hx⟩) (ne_top_of_dvr _)
    rw [if_pos ⟨h1, h3⟩, if_pos h1]
    subst h1
    obtain ⟨e₁, -, he₁⟩ := exists_vord_map c V
    obtain ⟨e₂, -, he₂⟩ := exists_vord_map φ V
    rw [← h4] at he₁
    have hp₁ : (p : F') ≠ 0 := by
      rw [← map_natCast ε]; exact (map_ne_zero ε).2 (Nat.cast_ne_zero.2 hp)
    have hp₂ : (p : K) ≠ 0 := by
      rw [← map_natCast k]; exact (map_ne_zero k).2 (Nat.cast_ne_zero.2 hp)
    have h5 := he₁ p hp₁
    have h6 := he₂ p hp₂
    rw [map_natCast] at h5 h6
    rw [he₁ π hπ, he₂ a ha]
    linear_combination (vord (V.comap φ) a * (vdeg φ V : ℤ) * vord O π) * (h5 - h6)
  · rw [if_neg fun h => h3 h.2, if_pos h1]
    have h4 : V.comap c ≠ O := fun h => h3 fun o => (h.ge o.2 : (o : F') ∈ V.comap c)
    obtain ⟨h5, h6⟩ := hπ' _ h2 h4
    rw [ValuationSubring.mem_comap, map_inv₀] at h6
    rw [vord_eq_zero_of_mem V ((map_ne_zero c).2 hπ) h5 h6]
    simp

private theorem count_alg (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) [Fact p.Prime]
    (hp : (p : 𝓞 F) ∈ v.asIdeal) (F' : Type) [Field F'] [NumberField F'] (ε : F →+* F') (O : ValuationSubring F')
    [IsDiscreteValuationRing O] [CharP (ResidueField O) p] (b : 𝓞 F →+* O) (hb : IsUp v ε O b)
    (K : Type) [Field K] (k : F →+* K) (W : ValuationSubring K) [IsDiscreteValuationRing W]
    (hW : W.comap k = O.comap ε) (J : Type) [Fintype J] (L : J → Type) [∀ j, Field (L j)]
    (φ : ∀ j, K →+* L j) (hφ : ∀ j, (φ j).Finite) (c : ∀ j, F' →+* L j) (hc : ∀ j, (φ j).comp k = (c j).comp ε)
    (n : ℕ) (hN : ∀ x : F', ∏ j, rnorm (φ j) (c j x) = k (rnorm ε x) ^ n) (a : K) (ha : a ≠ 0) :
    placeDeg p v * ∑ j, ((∑ᶠ V : ValuationSubring (L j),
        if V.comap (φ j) = W ∧ ∀ o : O, c j o ∈ V then vord V (φ j a) * (vdeg (φ j) V : ℤ) else 0 : ℤ) : ℝ) =
      (n : ℝ) * ((ramIdx O p : ℝ) * (resDeg O p : ℝ)) * (vord W a : ℝ) := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  obtain ⟨hW₀, hC⟩ := UpperTheory.place_degree_residue_formula F v p hp F' ε O b hb
  have : CharZero K := charZero_of_injective_ringHom k.injective
  have hε : ε.Finite := by
    letI := ε.toAlgebra
    have : IsScalarTower ℚ F F' := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    exact Module.Finite.of_restrictScalars_finite ℚ F F'
  obtain ⟨hs, hD, hn⟩ := UpperTheory.valuation_norm_sum_extensions F F' ε hε (O.comap ε)
  obtain ⟨π, hπ, hπO, hπ'⟩ := UpperTheory.exists_approximation_valuations F' O (ne_top_of_dvr O) _ hs fun V hV =>
    have := hD V hV; ne_top_of_dvr V
  have h1 : vord (O.comap ε) (rnorm ε π) = vord O π * (vdeg ε O : ℤ) := by
    rw [hn π hπ, finsum_eq_single _ O, if_pos rfl]
    intro V hV
    split_ifs with h
    · rw [vord_eq_zero_of_mem V hπ (hπ' V h hV).1 (hπ' V h hV).2, zero_mul]
    · rfl
  have hnz : ∀ {A B : Type} [Field A] [Field B] (ψ : A →+* B), ψ.Finite → ∀ x : B, x ≠ 0 → rnorm ψ x ≠ 0 :=
    fun ψ _ x hx => ((Ne.isUnit hx).map (rnorm ψ)).ne_zero
  have : IsDiscreteValuationRing (W.comap k) := hW ▸ hW₀
  obtain ⟨e₀, he₀, he⟩ := exists_vord_map k W
  rw [hW] at he
  have h2 (j : J) : (∑ᶠ V : ValuationSubring (L j),
        if V.comap (φ j) = W ∧ ∀ o : O, c j o ∈ V then vord V (φ j a) * (vdeg (φ j) V : ℤ) else 0 : ℤ) *
        (vord O π * vord W p) = vord W (rnorm (φ j) (c j π)) * (vord O p * vord W a) := by
    obtain ⟨-, hD', hn'⟩ := UpperTheory.valuation_norm_sum_extensions K (L j) (φ j) (hφ j) W
    rw [hn' _ ((map_ne_zero _).2 hπ), finsum_mul, finsum_mul]
    exact finsum_congr fun V => one_term ε k (φ j) (c j) (hc j) O W hW hD hD' hπ hπ' hp0 ha V
  have h3 : ∑ j, vord W (rnorm (φ j) (c j π)) = n * (e₀ * (vord O π * (vdeg ε O : ℤ))) := by
    rw [← vord_prod W _ _ fun j _ => hnz _ (hφ j) _ ((map_ne_zero _).2 hπ), hN, vord_pow, he _ (hnz _ hε _ hπ), h1]
  have h4 := Finset.sum_congr (s₁ := Finset.univ) rfl fun j _ => h2 j
  rw [← Finset.sum_mul, ← Finset.sum_mul, h3] at h4
  have h5 := he p (Nat.cast_ne_zero.2 hp0)
  rw [map_natCast] at h5
  have h6 : 0 < vord (O.comap ε) (p : F) := by
    refine vord_pos _ (Nat.cast_ne_zero.2 hp0) ((mem_nonunits_comap ε O _).2 ?_)
    have := ValuationSubring.coe_mem_nonunits_iff.2 ((hb.2 p).1 hp)
    simpa using this
  have h7 : 0 < vord O π := vord_pos O hπ hπO
  have h8 : vord O (p : F') = ramIdx O p := by
    have := vord_coe O (a := (p : O)) (Nat.cast_ne_zero.2 hp0)
    simpa [ramIdx] using this
  rw [← Int.cast_sum]
  generalize (∑ j : J, _ : ℤ) = S at h4 ⊢
  rw [h5, h8] at h4
  have h9 : S * vord (O.comap ε) (p : F) = n * (vdeg ε O : ℤ) * (ramIdx O p * vord W a) := by
    apply mul_left_cancel₀ (mul_pos he₀ h7).ne'
    linear_combination h4
  have h10 : (S : ℝ) * (vord (O.comap ε) (p : F) : ℝ) = n * (vdeg ε O : ℝ) * (ramIdx O p * (vord W a : ℝ)) := by
    exact_mod_cast h9
  have h11 : (0 : ℝ) < (vord (O.comap ε) (p : F) : ℝ) := by exact_mod_cast h6
  apply mul_right_cancel₀ h11.ne'
  linear_combination placeDeg p v * h10 + (n * (ramIdx O p : ℝ) * (vord W a : ℝ)) * hC

private theorem sp_fnMap {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X'] (g : X' ⟶ X)
    (hg : g (genericPoint X') ⤳ genericPoint X) :
    Spec.map (CommRingCat.ofHom (SmallSec.fnMap g hg)) ≫ genericFieldPoint X = genericFieldPoint X' ≫ g := by
  refine (congrArg (· ≫ X.fromSpecStalk (genericPoint X)) (Spec.map_comp _ _)).trans ?_
  rw [Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]
  rfl

private theorem fnMap_toFF {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X'] (g : X' ⟶ X)
    (hg : g (genericPoint X') ⤳ genericPoint X) {A B : Type} [CommRing A] [CommRing B] (p : X ⟶ Sp A)
    (q : X' ⟶ Sp B) (b : A →+* B) (w : g ≫ p = q ≫ spMap b) (a : A) :
    SmallSec.fnMap g hg (toFunctionField p a) = toFunctionField q (b a) := by
  have e : Spec.map (CommRingCat.ofHom (toFunctionField p) ≫ CommRingCat.ofHom (SmallSec.fnMap g hg)) =
      Spec.map (CommRingCat.ofHom b ≫ CommRingCat.ofHom (toFunctionField q)) := by
    rw [Spec.map_comp, Spec.map_comp, ← genericFieldPoint_over, ← genericFieldPoint_over, ← Category.assoc,
      sp_fnMap, Category.assoc, w, Category.assoc]
  exact congr($(Spec.map_injective e) a)

private theorem toFF_mem_nonunits {X : Scheme.{0}} [IsIntegral X] {A : Type} [CommRing A] (p : X ⟶ Sp A) {x : X}
    {W : ValuationSubring X.functionField} (h : DominatesStalk W x) (a : A) :
    toFunctionField p a ∈ W.nonunits ↔ a ∈ (p x).asIdeal := by
  obtain ⟨ψ, _, hψ⟩ := dominatesStalk_iff_exists_isLocalHom.1 h
  have _ : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  have e : toFunctionField p a = algebraMap _ X.functionField
      (X.presheaf.germ ⊤ x trivial (p.appTop ((Scheme.ΓSpecIso (.of A)).inv a))) :=
    (Scheme.algebraMap_germ_eq_germToFunctionField X (U := ⊤) (x := x) trivial _).symm
  rw [e, ← hψ, ValuationSubring.coe_mem_nonunits_iff, mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff,
    ← Scheme.mem_basicOpen_top, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  exact not_not

private theorem phi_comp {F : Type} [Field F] [NumberField F] {Y : Var F} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {b : 𝓞 F →+* O} {T : Vert.Model O} (μ : Match Y b T) (Q : TrueGeo.Model Y)
    [IsIntegral Q.X] (g : T.X ⟶ Q.X) (hg : g (genericPoint T.X) ⤳ genericPoint Q.X) (h : Extends μ Q g) :
    μ.φ.comp (SmallSec.fnMap Q.j (SmallSec.j_gen_specializes Q)) = SmallSec.fnMap g hg := by
  have e : Spec.map (CommRingCat.ofHom (SmallSec.fnMap Q.j (SmallSec.j_gen_specializes Q)) ≫
      CommRingCat.ofHom μ.φ) ≫ genericFieldPoint Q.X =
      Spec.map (CommRingCat.ofHom (SmallSec.fnMap g hg)) ≫ genericFieldPoint Q.X := by
    rw [Spec.map_comp, Category.assoc, sp_fnMap, sp_fnMap, ← Category.assoc]
    refine (congrArg (· ≫ Q.j) μ.φ_spec.symm).trans ?_
    rw [Category.assoc, ← h.1, ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
    rfl
  have : Mono (genericFieldPoint Q.X) := inferInstanceAs (Mono (Q.X.fromSpecStalk _))
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 e))

theorem UpperTheory.normal_model_complex_compat :
    ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) [Fact p.Prime], (p : 𝓞 F) ∈ v.asIdeal → ∀ (F' : Type) [Field F'] [NumberField F'] (ε : F →+* F') (O : ValuationSubring F') [IsDiscreteValuationRing O] [CharP (ResidueField O) p] (b : 𝓞 F →+* O), IsUp v ε O b → ∀ (σ : F' →+* ℂ) (Q : TrueGeo.Model Y) [IsIntegral Q.X] [IsLocallyNoetherian Q.X], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Q.X → ∀ (J : Type) [Fintype J] (T : J → Vert.Model O), (∀ j, GlobalTheory.IsNormalScheme (T j).X) → (∀ j, (T j).relDim = Y.dim) → ∀ (μ : ∀ j, Match Y b (T j)) (g : ∀ j, (T j).X ⟶ Q.X) (hg : ∀ j, g j (genericPoint (T j).X) ⤳ genericPoint Q.X), (∀ j, Extends (μ j) Q (g j)) → ∀ n : ℕ, 0 < n → Count μ ε σ n → ∀ η : Q.X, (Q.p η).asIdeal = v.asIdeal → Order.coheight η = 1 → ∀ a : Q.X.functionField, a ≠ 0 → placeDeg p v * ∑ j, ((∑ᶠ ζ : (T j).X, if g j ζ = η then Scheme.ord (SmallSec.fnMap (g j) (hg j) a) ζ * ((g j).residueDegree ζ : ℤ) else 0 : ℤ) : ℝ) = (n : ℝ) * ((ramIdx O p : ℝ) * (resDeg O p : ℝ)) * (Scheme.ord a η : ℝ) := by
  intro F _ _ Y v p _ hp F' _ _ ε O _ _ b hb σ Q _ _ hQ J _ T hT _ μ g hg hE n hn hC η hη hη1 a ha
  have := GlobalTheory.IsNormalScheme.of_pred hQ
  have hpr : IsProper Q.p := (isProper_and_exists_isAmpleLB_of_isProjOver Q.ar.isProjOver).1
  have hsep : Q.X.IsSeparated := ⟨by rw [← terminal.comp_from Q.p]; infer_instance⟩
  have := SmallSec.isPreimmersion_j Q
  let e : Q.X.functionField ≃+* Y.Fn := RingEquiv.ofBijective (SmallSec.fnMap Q.j (SmallSec.j_gen_specializes Q))
    ⟨RingHom.injective _, SmallSec.fnMap_surjective _ _⟩
  let k : F →+* Q.X.functionField := e.symm.toRingHom.comp (algebraMap F Y.Fn)
  have hY (x : F) : algebraMap F Y.Fn x = toFunctionField Y.str x :=
    IsScalarTower.algebraMap_apply F Γ(Y.X, ⊤) Y.Fn x
  have hk (x : 𝓞 F) : k x = toFunctionField Q.p x := by
    refine e.symm_apply_eq.2 ?_
    rw [hY]
    exact (fnMap_toFF Q.j _ Q.p Y.str _ Q.pb.w x).symm
  have hφ (j : J) (x : Q.X.functionField) : (μ j).φ (e x) = SmallSec.fnMap (g j) (hg j) x :=
    congr($(phi_comp (μ j) Q (g j) (hg j) (hE j)) x)
  have hinj (j : J) : Function.Injective (cst (T j)) := by
    rw [injective_iff_map_eq_zero]
    intro o ho
    by_contra h0
    exact ((T j).isRegularFn_const h0).ne_zero
      (germ_injective_of_isIntegral (T j).X (genericPoint _) (U := ⊤) trivial (ho.trans (map_zero _).symm))
  let c (j : J) : F' →+* (T j).X.functionField := IsFractionRing.lift (hinj j)
  have hc (j : J) (o : O) : c j o = toFunctionField (T j).str o := IsFractionRing.lift_algebraMap (hinj j) o
  have hcomp (j : J) : (SmallSec.fnMap (g j) (hg j)).comp k = (c j).comp ε := by
    refine IsFractionRing.ringHom_ext (A := 𝓞 F) fun x => ?_
    change SmallSec.fnMap (g j) (hg j) (k x) = c j (ε x)
    rw [hk, ← hb.1, hc]
    exact fnMap_toFF (g j) _ Q.p (T j).str b (hE j).2 x
  have : Countable F := Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm
  have : Countable F' := Countable.of_equiv _ (Module.finBasis ℚ F').equivFun.toEquiv.symm
  have : Countable (𝓞 F) := RingOfIntegers.coe_injective.countable
  have := UpperTheory.countable_functionField_finiteType (𝓞 F) Q.X Q.p
  have (j : J) := UpperTheory.countable_functionField_finiteType O (T j).X (T j).str
  obtain ⟨hfin, hN⟩ := UpperTheory.embedding_count_extensions F F' ε σ Q.X.functionField k J (fun j => (T j).X.functionField)
    (fun j => SmallSec.fnMap (g j) (hg j)) c hcomp n hn fun ι hι => by
      rw [← hC (ι.comp e.symm.toRingHom) hι]
      refine Nat.card_congr (Equiv.subtypeEquivRight fun q => and_congr ?_ ?_)
      · constructor
        · rintro rfl
          ext y
          obtain ⟨x, rfl⟩ := e.surjective y
          simp [hφ]
        · intro h
          ext x
          simpa [hφ] using congr($h (e x))
      · constructor
        · intro h
          ext o
          exact (congrArg q.2 (hc _ o)).symm.trans congr($h o)
        · intro h
          refine IsFractionRing.ringHom_ext (A := O) fun o => ?_
          exact (congrArg q.2 (hc _ o)).trans congr($h o)
  obtain ⟨W, hW⟩ := exists_dominatesStalk η
  have := hW.isDiscreteValuationRing hη1
  have hWk : W.comap k = O.comap ε := by
    refine UpperTheory.valuationSubring_unique_of_prime F v _ _ (fun x => ?_) fun x => ?_
    · rw [mem_nonunits_comap, hk, toFF_mem_nonunits Q.p hW, hη]
    · rw [mem_nonunits_comap, ← hb.1, ValuationSubring.coe_mem_nonunits_iff, hb.2]
  have : CharZero Q.X.functionField := charZero_of_injective_ringHom k.injective
  rw [UpperTheory.order_eq_valuation_codim_one Q.X η W hη1 hW a, ← count_alg F v p hp F' ε O b hb Q.X.functionField k W hWk J
    (fun j => (T j).X.functionField) (fun j => SmallSec.fnMap (g j) (hg j)) hfin c hcomp n hN a ha]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have := hT j
  rw [UpperTheory.order_codim_one_finite_map Q.X (T j).X O (T j).str (g j) (hg j) (hfin j) η W hη1 hW]
  simp only [hc]
