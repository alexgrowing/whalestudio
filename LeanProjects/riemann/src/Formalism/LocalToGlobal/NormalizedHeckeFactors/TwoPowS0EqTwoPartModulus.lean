import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain ReciprocityTheory.Gal

namespace Formalism.L2

section Points

variable {O X : Type} [CommRing O] [IsDomain O] [Fintype X]

def evPt (T : Subalgebra O (X → O)) (x : X) : T →ₐ[O] O :=
  (Pi.evalAlgHom O (fun _ : X => O) x).comp T.val

@[simp] theorem evPt_apply (T : Subalgebra O (X → O)) (x : X) (f : T) : evPt T x f = (f : X → O) x := rfl

theorem evPt_injective (T : Subalgebra O (X → O))
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → O) x ≠ (f : X → O) y) : Function.Injective (evPt T) := by
  intro x y hxy
  by_contra hne
  obtain ⟨f, hf, hfxy⟩ := hsep x y hne
  exact hfxy (congrArg (fun φ : T →ₐ[O] O => φ ⟨f, hf⟩) hxy)

theorem exists_delta (T : Subalgebra O (X → O))
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → O) x ≠ (f : X → O) y) (x : X) :
    ∃ P : T, (P : X → O) x ≠ 0 ∧ ∀ y, y ≠ x → (P : X → O) y = 0 := by
  classical
  have key : ∀ y, y ≠ x → ∃ g ∈ T, g x ≠ 0 ∧ g y = 0 := by
    intro y hy
    obtain ⟨f, hf, hne⟩ := hsep x y (Ne.symm hy)
    refine ⟨f - algebraMap O (X → O) (f y), T.sub_mem hf (T.algebraMap_mem _), ?_, ?_⟩
    · simpa [sub_eq_zero] using hne
    · simp
  choose g hgT hgx hgy using key
  let e : X → T := fun y => if hy : y = x then 1 else ⟨g y hy, hgT y hy⟩
  refine ⟨∏ y, e y, ?_, ?_⟩
  · simp only [SubmonoidClass.coe_finset_prod, Finset.prod_apply]
    refine Finset.prod_ne_zero_iff.mpr fun y _ => ?_
    by_cases hy : y = x
    · simp [e, hy]
    · simp [e, hy, hgx y hy]
  · intro y hy
    simp only [SubmonoidClass.coe_finset_prod, Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ y) (by simp [e, hy, hgy y hy])

theorem evPt_surjective (T : Subalgebra O (X → O))
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → O) x ≠ (f : X → O) y) : Function.Surjective (evPt T) := by
  classical
  intro φ
  choose P hPx hPy using exists_delta T hsep
  set N : O := ∏ y, ((P y : T) : X → O) y with hN
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.mpr fun y _ => hPx y
  let c : X → O := fun x => ∏ y ∈ Finset.univ.erase x, ((P y : T) : X → O) y
  have hsum : (∑ x, c x • P x : T) = algebraMap O T N := by
    apply Subtype.ext
    funext z
    have hR : ((algebraMap O T N : T) : X → O) z = N := by simp
    rw [hR]
    simp only [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single z (fun x _ hxz => by rw [hPy x z (fun h => hxz h.symm), mul_zero])
      (fun h => absurd (Finset.mem_univ z) h)]
    exact Finset.prod_erase_mul _ _ (Finset.mem_univ z)
  have hφ : ∃ x, φ (P x) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have h1 := congrArg φ hsum
    rw [AlgHom.commutes] at h1
    exact hN0 (by simpa [hcon] using h1.symm)
  obtain ⟨x0, hx0⟩ := hφ
  refine ⟨x0, AlgHom.ext fun g => ?_⟩
  have hmul : g * P x0 = ((g : X → O) x0) • P x0 := by
    apply Subtype.ext
    funext z
    by_cases hz : z = x0
    · subst hz
      simp
    · simp [hPy x0 z hz]
  have h2 := congrArg φ hmul
  rw [map_mul, map_smul, smul_eq_mul] at h2
  have h3 := mul_right_cancel₀ hx0 h2
  rw [evPt_apply]
  exact h3.symm

def ptsEquiv (T : Subalgebra O (X → O))
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → O) x ≠ (f : X → O) y) : X ≃ (T →ₐ[O] O) :=
  Equiv.ofBijective (evPt T) ⟨evPt_injective T hsep, evPt_surjective T hsep⟩

end Points

section Record

variable (D : D7)

def ptsNd (i : D.nd.Loc) : D.nd.X i ≃ (D.nd.T i →ₐ[D.nd.O i] D.nd.O i) :=
  ptsEquiv (D.nd.T i) (D.nd.T_sep i)

@[simp] theorem ptsNd_apply (i : D.nd.Loc) (x : D.nd.X i) (f : D.nd.T i) :
    ptsNd D i x f = (f : D.nd.X i → D.nd.O i) x := rfl

theorem Z_eq (i : D.nd.Loc) : (↑(D.nd.Z i) : Set (D.nd.X i)) = Formalism.MainNotions.N.ZN D.nd D.naut i :=
  Set.ext (D.Z_tie i)

theorem Zgood_eq (i : D.nd.Loc) : (↑(D.nd.Zgood i) : Set (D.nd.X i)) = Formalism.MainNotions.N.ZgoodN D.nd D.naut i :=
  Set.ext (D.Zgood_tie i)

theorem zgoodSub : D.nd.ZgoodSub := fun i x hx =>
  (D.Z_tie i x).2 ((D.Zgood_tie i x).1 hx).1

theorem mem_cc_iff (i : D.nd.Loc) (f : D.nd.T i) :
    f ∈ D.nd.cc i ↔ ∀ x, x ∉ Formalism.MainNotions.N.ZN D.nd D.naut i → (f : D.nd.X i → D.nd.O i) x = 0 := by
  simp only [NData.cc, ccIdeal, RingHom.mem_ker, RingHom.comp_apply]
  constructor
  · intro h x hx
    have := congrFun h ⟨x, fun hz => hx ((D.Z_tie i x).1 hz)⟩
    simpa using this
  · intro h
    funext y
    simpa using h y.1 (fun hz => y.2 ((D.Z_tie i y.1).2 hz))

theorem mem_cc_iff_pts (i : D.nd.Loc) (f : D.nd.T i) :
    f ∈ D.nd.cc i ↔ ∀ φ : D.nd.T i →ₐ[D.nd.O i] D.nd.O i,
      (ptsNd D i).symm φ ∉ Formalism.MainNotions.N.ZN D.nd D.naut i → φ f = 0 := by
  rw [mem_cc_iff]
  constructor
  · intro h φ hφ
    have h1 := h _ hφ
    rw [← ptsNd_apply, Equiv.apply_symm_apply] at h1
    exact h1
  · intro h x hx
    have h1 := h (ptsNd D i x) (by rwa [Equiv.symm_apply_apply])
    rwa [ptsNd_apply] at h1

def etaOf (i : D.nd.Loc) (Y : Set (D.nd.X i)) : ℚ :=
  let up := (D.nd.eigSum i Y).restrictScalars (D.nd.O i) ⊓
    (D.nd.MtIn i ⊔ (D.nd.eigSum i Yᶜ).restrictScalars (D.nd.O i))
  let low := D.nd.MtIn i ⊓ (D.nd.eigSum i Y).restrictScalars (D.nd.O i)
  lenUnit (O := D.nd.O i) (D.nd.l i) (↥up ⧸ low.comap up.subtype)

theorem etaLoc_eq (i : D.nd.Loc) : D.nd.etaLoc i = etaOf D i (Formalism.MainNotions.N.ZgoodN D.nd D.naut i) := by
  rw [← Zgood_eq]; rfl

theorem mem_MtUp_iff (i : D.nd.Loc) (y : TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i)) :
    y ∈ D.nd.MtUp i ↔ y ∈ D.nd.eigSum i (Formalism.MainNotions.N.ZgoodN D.nd D.naut i) ∧
      ∃ m ∈ D.nd.MtIn i, ∃ z ∈ D.nd.eigSum i (Formalism.MainNotions.N.ZgoodN D.nd D.naut i)ᶜ, m + z = y := by
  simp only [NData.MtUp, Zgood_eq, Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_sup]

theorem s0_eq (i : D.nd.Loc) : D.nd.s0 i = max 1 (D.host.QS.factorization (D.nd.l i)) := by
  by_cases h : D.nd.l i = 2
  · have h1 : 1 ≤ D.host.QS.factorization 2 :=
      (Nat.prime_two.dvd_iff_one_le_factorization D.host.QS_pos.ne').1
        ((dvd_pow_self 2 (Nat.succ_ne_zero _)).trans D.host.tower_dvd)
    rw [D.nd.restNLevelExponent_of_two i h, h, max_eq_right h1]
  · exact D.nd.restNLevelExponent_of_odd i h

theorem two_pow_s0_eq_two_part_modulus (i : D.nd.Loc) (h : D.nd.l i = 2) : 2 ^ D.nd.s0 i = ordProj[2] D.host.QS := by
  rw [D.nd.restNLevelExponent_of_two i h]

theorem vdel_eq (i : D.nd.Loc) : D.nd.vdel i = ∑ k ∈ Finset.Ioo 0 D.R.t,
    (((max 1 (D.host.QS.factorization (D.nd.l i)) : ℕ) : ℚ) + (padicValNat (D.nd.l i) k : ℚ)) := by
  unfold NData.vdel
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [s0_eq]

theorem mem_S_iff (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E)) : v ∈ D.nd.S i ↔
    (v ∈ placesOver D.host.E (D.host.g 0) ∨ v ∈ placesOver D.host.E (D.host.g 1) ∨
      v ∈ placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde)) ∧
      v ∉ placesOver D.host.E (D.nd.l i) :=
  D.nd.S_def i v

theorem mem_Q_iff (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E)) :
    v ∈ D.nd.Q i ↔ ∃ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), D.ntw.psiL i σ ≠ 1 :=
  (D.ntw.psiL_ram i v (D.nd.plOm.1 v) (D.nd.plOm.2 v)).symm

end Record

section Good

open Polynomial

theorem isGood_pair_congr {N g : ℕ} [Fact g.Prime] {PP J : Type} (f : PP → (ZMod g)[X])
    (χ χ' : PP → J → (ZMod g)ˣ) (h : ∀ v j, χ' v j = χ v j ∨ χ' v j = (χ v j)⁻¹) :
    (Formalism.CyclotomicNorms.IsGood N g f χ' ∧ Formalism.CyclotomicNorms.IsGood N g f (fun v j => (χ' v j)⁻¹)) ↔
      (Formalism.CyclotomicNorms.IsGood N g f χ ∧ Formalism.CyclotomicNorms.IsGood N g f (fun v j => (χ v j)⁻¹)) := by
  have key : ∀ (a b : PP → J → (ZMod g)ˣ), (∀ v j, b v j = a v j ∨ b v j = (a v j)⁻¹) →
      Formalism.CyclotomicNorms.IsGood N g f a → Formalism.CyclotomicNorms.IsGood N g f (fun v j => (a v j)⁻¹) →
      Formalism.CyclotomicNorms.IsGood N g f b ∧ Formalism.CyclotomicNorms.IsGood N g f (fun v j => (b v j)⁻¹) := by
    intro a b hab ha ha'
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ha
    obtain ⟨-, -, -, h4', -, -⟩ := ha'
    refine ⟨⟨h1, h2, h3, ?_, h5, h6⟩, ⟨h1, h2, h3, ?_, h5, h6⟩⟩
    · intro ℓ hℓ hg v j x hx
      rcases hab v j with e | e <;> rw [e]
      · exact h4 ℓ hℓ hg v j x hx
      · exact h4' ℓ hℓ hg v j x hx
    · intro ℓ hℓ hg v j x hx
      rcases hab v j with e | e <;> simp only [e, inv_inv]
      · exact h4' ℓ hℓ hg v j x hx
      · exact h4 ℓ hℓ hg v j x hx
  constructor
  · rintro ⟨hg, hg'⟩
    exact key χ' χ (fun v j => by rcases h v j with e | e <;> simp [e]) hg hg'
  · rintro ⟨hg, hg'⟩
    exact key χ χ' h hg hg'

theorem goodRow_congr (D : D7) (σ : D.what₂.FT) (χ' : ∀ k, D.nd.PlG k → Fin D.R.m → (ZMod (D.host.g k))ˣ)
    (h : ∀ k v j, χ' k v j = D.nd.chiT k v j ∨ χ' k v j = (D.nd.chiT k v j)⁻¹) :
    D.nd.goodRow σ ↔ ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      Formalism.CyclotomicNorms.IsGood D.R.r (D.host.g k) (D.nd.lab k σ) (χ' k) ∧
      Formalism.CyclotomicNorms.IsGood D.R.r (D.host.g k) (D.nd.lab k σ) (fun v j => (χ' k v j)⁻¹) := by
  unfold NData.goodRow
  refine forall_congr' fun k => ?_
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  exact (isGood_pair_congr _ _ _ (h k)).symm

theorem qchi_congr (D : D7) (χ' : ∀ k, D.nd.PlG k → Fin D.R.m → (ZMod (D.host.g k))ˣ)
    (h : ∀ k v j, χ' k v j = D.nd.chiT k v j ∨ χ' k v j = (D.nd.chiT k v j)⁻¹) :
    IntermediateField.adjoin ℚ {z | ∃ (k : Fin 2) (v : D.nd.PlG k) (j : Fin D.R.m),
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      z = D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
        ((χ' k v j : ZMod (D.host.g k))))} = D.ntypes.Qchi := by
  have key : ∀ k (u : (ZMod (D.host.g k))ˣ),
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
          (((u⁻¹ : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)))) =
        (D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
          ((u : ZMod (D.host.g k)))))⁻¹ := by
    intro k u
    have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
  unfold NTypes.Qchi
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro z ⟨k, v, j, rfl⟩
    rcases h k v j with e | e
    · exact IntermediateField.subset_adjoin _ _ ⟨k, v, j, by rw [e]⟩
    · rw [e, key]
      exact inv_mem (IntermediateField.subset_adjoin _ _ ⟨k, v, j, rfl⟩)
  · rw [IntermediateField.adjoin_le_iff]
    rintro z ⟨k, v, j, rfl⟩
    rcases h k v j with e | e
    · exact IntermediateField.subset_adjoin _ _ ⟨k, v, j, by rw [e]⟩
    · have e' : D.nd.chiT k v j = (χ' k v j)⁻¹ := by rw [e, inv_inv]
      rw [e', key]
      exact inv_mem (IntermediateField.subset_adjoin _ _ ⟨k, v, j, rfl⟩)

end Good

section Tame

theorem span_pow_sub_one {A : Type} [CommRing A] (ζ : A) (n a : ℕ) (hn : ζ ^ n = 1) (ha : Nat.Coprime a n) :
    Ideal.span {ζ ^ a - 1} = Ideal.span {ζ - 1} := by
  apply le_antisymm
  · rw [Ideal.span_singleton_le_span_singleton]
    simpa [one_pow] using sub_dvd_pow_sub_pow ζ 1 a
  · rw [Ideal.span_singleton_le_span_singleton]
    rcases Nat.lt_or_ge 1 n with h1 | h1
    · haveI : NeZero n := ⟨by omega⟩
      obtain ⟨m, hm⟩ : ∃ m, a * m % n = 1 := by
        refine ⟨((ZMod.unitOfCoprime a ha)⁻¹ : (ZMod n)ˣ).val.val, ?_⟩
        have h2 : ((a * ((ZMod.unitOfCoprime a ha)⁻¹ : (ZMod n)ˣ).val.val : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) := by
          simp only [Nat.cast_mul, Nat.cast_one, ZMod.natCast_zmod_val]
          have h3 := (ZMod.unitOfCoprime a ha).mul_inv
          rwa [ZMod.coe_unitOfCoprime] at h3
        rw [ZMod.natCast_eq_natCast_iff'] at h2
        rw [h2, Nat.mod_eq_of_lt h1]
      have hz : (ζ ^ a) ^ m = ζ := by
        rw [← pow_mul, ← Nat.div_add_mod (a * m) n, hm, pow_add, pow_mul, hn, one_pow, one_mul, pow_one]
      calc ζ ^ a - 1 ∣ (ζ ^ a) ^ m - 1 := by simpa [one_pow] using sub_dvd_pow_sub_pow (ζ ^ a) 1 m
        _ = ζ - 1 := by rw [hz]
    · interval_cases n
      · rw [Nat.coprime_zero_right] at ha
        subst ha
        simp
      · rw [pow_one] at hn
        subst hn
        simp

theorem lenUnit_pow_sub_one {O : Type} [CommRing O] (l : ℕ) (ζ : O) (n a : ℕ) (hn : ζ ^ n = 1)
    (ha : Nat.Coprime a n) :
    lenUnit (O := O) l (O ⧸ Ideal.span {ζ ^ a - 1}) = lenUnit (O := O) l (O ⧸ Ideal.span {ζ - 1}) := by
  rw [span_pow_sub_one ζ n a hn ha]

end Tame

def latRel {O : Type} [CommRing O] {φ : O →+* ℂ} {V : Type} [AddCommGroup V] [Module ℂ V] (L : Rows.OLat O φ V) :
    Set (L.gen → O) :=
  {r | ∑ g : L.gen, φ (r g) • (g : V) = 0}

def latRelSub {O : Type} [CommRing O] {φ : O →+* ℂ} {V : Type} [AddCommGroup V] [Module ℂ V] (L : Rows.OLat O φ V) :
    Submodule O (L.gen → O) where
  carrier := latRel L
  zero_mem' := by simp [latRel]
  add_mem' := by
    intro a b ha hb
    simp only [latRel, Set.mem_ofPred_eq, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib] at ha hb ⊢
    rw [ha, hb, add_zero]
  smul_mem' := by
    intro c a ha
    simp only [latRel, Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul] at ha ⊢
    rw [← Finset.smul_sum, ha, smul_zero]

@[simp] theorem mem_latRelSub {O : Type} [CommRing O] {φ : O →+* ℂ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (L : Rows.OLat O φ V) (r : L.gen → O) : r ∈ latRelSub L ↔ r ∈ latRel L := Iff.rfl

def MjLatRank (D : D7) : Prop :=
  ∀ i : D.nd.Loc, Module.finrank D.what₂.O (((D.what₂.MjLat (D.nd.j i)).gen → D.what₂.O) ⧸ latRelSub (D.what₂.MjLat (D.nd.j i))) =
    Module.finrank ℂ (D.what₂.Mj (D.nd.j i))

def plF (D : D7) (k : Fin 2) : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) :=
  {v | ((D.host.g k : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ v.asIdeal}

def plGF (D : D7) (k : Fin 2) (v : D.nd.PlG k) : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) where
  asIdeal := (D.naut.plGw k v).asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := Ideal.under_ne_bot _ (D.naut.plGw k v).ne_bot

theorem plGF_over (D : D7) (k : Fin 2) (v : D.nd.PlG k) : NG.OverPl (D.naut.plGw k v) (plGF D k v) := rfl

theorem plGF_mem (D : D7) (k : Fin 2) (v : D.nd.PlG k) : plGF D k v ∈ plF D k := by
  have h := D.naut.plGw_over k v
  show ((D.host.g k : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈
    (D.naut.plGw k v).asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))
  rw [Ideal.mem_comap, map_natCast]
  exact h

def plGFs (D : D7) (k : Fin 2) (v : D.nd.PlG k) : plF D k := ⟨plGF D k v, plGF_mem D k v⟩

theorem plGF_unique (D : D7) (k : Fin 2) (v : D.nd.PlG k)
    (u : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (h : NG.OverPl (D.naut.plGw k v) u) :
    u = plGF D k v :=
  HeightOneSpectrum.ext (h.symm.trans (plGF_over D k v))

def PlGBij (D : D7) : Prop := ∀ k, Function.Bijective (plGFs D k)

def plGEquiv {D : D7} (h : PlGBij D) (k : Fin 2) : D.nd.PlG k ≃ plF D k := Equiv.ofBijective (plGFs D k) (h k)

@[simp] theorem plGEquiv_apply {D : D7} (h : PlGBij D) (k : Fin 2) (v : D.nd.PlG k) :
    (plGEquiv h k v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) = plGF D k v := rfl

theorem embK_OtoLL_mem (D : D7) (i : D.nd.Loc) (y : D.what₂.O) :
    D.nd.embK i (D.what₂.OtoLL y) ∈ (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).range := by
  rw [← D.nd.embK_w i]
  by_cases h0 : D.what₂.OtoLL y = 0
  · rw [h0, AddValuation.map_zero]; exact le_top
  · rw [D.val_eq _ _ h0]
    have hint := D.O_int y
    set x : 𝓞 D.what₂.LL := ⟨D.what₂.OtoLL y, hint⟩
    have hx : (x : D.what₂.LL) = D.what₂.OtoLL y := rfl
    have hle := (D.plEq (D.nd.w i)).valuation_le_one (K := D.what₂.LL) x
    have hne : (D.plEq (D.nd.w i)).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL x) ≠ 0 := by
      simpa [hx] using h0
    unfold vAdd
    have : WithZero.log ((D.plEq (D.nd.w i)).valuation D.what₂.LL (D.what₂.OtoLL y)) ≤ 0 := by
      have hne' : (D.plEq (D.nd.w i)).valuation D.what₂.LL (D.what₂.OtoLL y) ≠ 0 := by simpa [hx] using hne
      have hle' : (D.plEq (D.nd.w i)).valuation D.what₂.LL (D.what₂.OtoLL y) ≤ 1 := by simpa [hx] using hle
      have h2 : WithZero.exp (WithZero.log ((D.plEq (D.nd.w i)).valuation D.what₂.LL (D.what₂.OtoLL y))) ≤
          WithZero.exp (0 : ℤ) := by
        rw [WithZero.exp_log hne']; simpa using hle'
      exact WithZero.exp_le_exp.mp h2
    exact_mod_cast (by omega : (0:ℤ) ≤ -WithZero.log ((D.plEq (D.nd.w i)).valuation D.what₂.LL (D.what₂.OtoLL y)))

def fracRangeEquiv (O : Type) [CommRing O] [IsDomain O] :
    O ≃+* (algebraMap O (FractionRing O)).range :=
  RingEquiv.ofBijective (algebraMap O (FractionRing O)).rangeRestrict
    ⟨fun _ _ h => IsFractionRing.injective O (FractionRing O) (congrArg Subtype.val h),
     (algebraMap O (FractionRing O)).rangeRestrict_surjective⟩

def sOf (D : D7) (i : D.nd.Loc) : D.what₂.O →+* D.nd.O i :=
  (fracRangeEquiv (D.nd.O i)).symm.toRingHom.comp
    (((D.nd.embK i).comp D.what₂.OtoLL).codRestrict _ (embK_OtoLL_mem D i))

theorem sOf_spec (D : D7) (i : D.nd.Loc) (y : D.what₂.O) :
    algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (sOf D i y) = D.nd.embK i (D.what₂.OtoLL y) := by
  have h := (fracRangeEquiv (D.nd.O i)).apply_symm_apply
    (((D.nd.embK i).comp D.what₂.OtoLL).codRestrict _ (embK_OtoLL_mem D i) y)
  exact congrArg Subtype.val h

theorem sOf_unique (D : D7) (i : D.nd.Loc) (s : D.what₂.O →+* D.nd.O i)
    (hs : ∀ y, algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (s y) = D.nd.embK i (D.what₂.OtoLL y)) :
    s = sOf D i := RingHom.ext fun y => IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))
    ((hs y).trans (sOf_spec D i y).symm)

structure NormalizedDataCompatibility (D : D7) where
  bj : ∀ i, (D.what₂.MjLat (D.nd.j i)).gen → D.nd.Bj i
  bj_span : ∀ i, Submodule.span (D.nd.O i) (Set.range (bj i)) = ⊤
  bj_rel : ∀ i (c : (D.what₂.MjLat (D.nd.j i)).gen → D.nd.O i), ∑ g, c g • bj i g = 0 ↔
    c ∈ Submodule.span (D.nd.O i) ((fun r => (sOf D i) ∘ r) '' latRel (D.what₂.MjLat (D.nd.j i)))

end Formalism.L2
