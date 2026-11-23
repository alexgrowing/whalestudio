import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace
import Development.AbelianVarietyTheory.Definitions.Divisors.PointSide
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyAlgHomEqMapMinpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDvdPowOfAevalEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbKEqZeroOfCharpolyNotSeparable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbKEqZeroOfCusp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolEqIdxRatio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicRealisationHolomorphicMap
open MeasureTheory Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.VanishNonEll

open GlobalTheory.BCT GlobalTheory.BCT.OrbProd GlobalTheory.LKCount GlobalTheory.LKCount.OrbKProd

section Transport

variable {A B : Type} [Group A] [Group B]

theorem map_twCent_id (e : A ≃* B) (δ : A) :
    (twCent (MonoidHom.id A) δ).map e.toMonoidHom = twCent (MonoidHom.id B) (e δ) := by
  ext b
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' : a * δ = δ * a := ha
    show e a * e δ = e δ * e a
    rw [← map_mul, ha', map_mul]
  · intro hb
    have hb' : b * e δ = e δ * b := hb
    refine ⟨e.symm b, ?_, by simp⟩
    show e.symm b * δ = δ * e.symm b
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hb']

theorem map_conj_equiv (e : A ≃* B) (K : Subgroup A) (x : A) :
    (K.map (MulAut.conj x).toMonoidHom).map e.toMonoidHom =
      (K.map e.toMonoidHom).map (MulAut.conj (e x)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext k
  simp [MulAut.conj_apply]

theorem orbK_congr_equiv (e : A ≃* B) (K : Subgroup A) (δ : A) (F : A → ℂ)
    (hinv : ∀ t ∈ twCent (MonoidHom.id B) (e δ), ∀ k ∈ K.map e.toMonoidHom, ∀ x,
      oTerm (MonoidHom.id B) (K.map e.toMonoidHom) (twCent (MonoidHom.id B) (e δ) ⊓ K.map e.toMonoidHom) (e δ)
          (fun z => F (e.symm z)) (t * x * k) =
        oTerm (MonoidHom.id B) (K.map e.toMonoidHom) (twCent (MonoidHom.id B) (e δ) ⊓ K.map e.toMonoidHom) (e δ)
          (fun z => F (e.symm z)) x) :
    orbK (MonoidHom.id A) K δ F = orbK (MonoidHom.id B) (K.map e.toMonoidHom) (e δ) (fun z => F (e.symm z)) := by
  unfold orbK
  rw [orbC_eq, orbC_eq]
  set TB := twCent (MonoidHom.id B) (e δ)
  set KB := K.map e.toMonoidHom
  have hmemT : ∀ a ∈ TB, e.symm a ∈ twCent (MonoidHom.id A) δ := by
    intro a ha
    rw [← show (twCent (MonoidHom.id A) δ).map e.toMonoidHom = TB from map_twCent_id e δ] at ha
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    simpa using ha'
  have hmemK : ∀ b ∈ KB, e.symm b ∈ K := by
    intro b hb
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    simpa using hb'
  have hpt : ∀ x : A, oTerm (MonoidHom.id A) K (twCent (MonoidHom.id A) δ ⊓ K) δ F x =
      oTerm (MonoidHom.id B) KB (TB ⊓ KB) (e δ) (fun z => F (e.symm z)) (e x) := by
    intro x
    unfold oTerm
    congr 1
    · have h1 : TB ⊓ KB = (twCent (MonoidHom.id A) δ ⊓ K).map e.toMonoidHom := by
        rw [Subgroup.map_inf_eq _ _ _ e.injective, map_twCent_id]
      have h2 : TB ⊓ KB.map (MulAut.conj (e x)).toMonoidHom =
          (twCent (MonoidHom.id A) δ ⊓ K.map (MulAut.conj x).toMonoidHom).map e.toMonoidHom := by
        rw [Subgroup.map_inf_eq _ _ _ e.injective, map_twCent_id, map_conj_equiv]
      rw [h1, h2]
      unfold vol
      rw [Subgroup.relIndex_map_map_of_injective _ _ e.injective,
        Subgroup.relIndex_map_map_of_injective _ _ e.injective]
    · simp
  let Φ : DoubleCoset.Quotient (twCent (MonoidHom.id A) δ : Set A) (K : Set A) →
      DoubleCoset.Quotient (TB : Set B) (KB : Set B) := fun q => DoubleCoset.mk TB KB (e (Quotient.out q))
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro q1 q2 h
      obtain ⟨a, ha, b, hb, h'⟩ := (DoubleCoset.eq _ _ _ _).mp h
      calc q1 = DoubleCoset.mk _ K (Quotient.out q1) := (DoubleCoset.out_eq' _ _ q1).symm
        _ = DoubleCoset.mk _ K (Quotient.out q2) := by
          rw [DoubleCoset.eq]
          refine ⟨e.symm a, hmemT a ha, e.symm b, hmemK b hb, ?_⟩
          apply e.injective
          simp [h']
        _ = q2 := DoubleCoset.out_eq' _ _ q2
    · intro p
      refine ⟨DoubleCoset.mk (twCent (MonoidHom.id A) δ) K (e.symm (Quotient.out p)), ?_⟩
      obtain ⟨a, b, ha, hb, h'⟩ := DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id A) δ) K (e.symm (Quotient.out p))
      show DoubleCoset.mk TB KB (e (Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id A) δ) K (e.symm (Quotient.out p))))) = p
      rw [h']
      conv_rhs => rw [← DoubleCoset.out_eq' TB KB p]
      rw [DoubleCoset.eq]
      have ha' : e a ∈ TB := by rw [← show (twCent (MonoidHom.id A) δ).map e.toMonoidHom = TB from map_twCent_id e δ]; exact Subgroup.mem_map_of_mem _ ha
      have hb' : e b ∈ KB := Subgroup.mem_map_of_mem _ hb
      refine ⟨(e a)⁻¹, TB.inv_mem ha', (e b)⁻¹, KB.inv_mem hb', ?_⟩
      simp [mul_assoc]
  have hz : ∀ q : DoubleCoset.Quotient (twCent (MonoidHom.id A) δ : Set A) (K : Set A), oTerm (MonoidHom.id A) K (twCent (MonoidHom.id A) δ ⊓ K) δ F (Quotient.out q) =
      oTerm (MonoidHom.id B) KB (TB ⊓ KB) (e δ) (fun z => F (e.symm z)) (Quotient.out (Equiv.ofBijective Φ hΦ q)) := by
    intro q
    rw [hpt]
    obtain ⟨a, b, ha, hb, h'⟩ := DoubleCoset.mk_out_eq_mul TB KB (e (Quotient.out q))
    show _ = oTerm (MonoidHom.id B) KB (TB ⊓ KB) (e δ) (fun z => F (e.symm z)) (Quotient.out (DoubleCoset.mk TB KB (e (Quotient.out q))))
    rw [h', hinv a ha b hb]
  rw [finsum_congr hz]
  exact finsum_comp_equiv (Equiv.ofBijective Φ hΦ)
    (f := fun q => oTerm (MonoidHom.id B) KB (TB ⊓ KB) (e δ) (fun z => F (e.symm z)) (Quotient.out q))

end Transport

section Prod

variable {G₁ G₂ : Type} [Group G₁] [Group G₂] [TopologicalSpace G₁] [TopologicalSpace G₂]
  [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]

theorem prodMap_id_eq : (MonoidHom.id G₁).prodMap (MonoidHom.id G₂) = MonoidHom.id (G₁ × G₂) := by
  ext <;> rfl

theorem oTerm_prod_inv (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (δ₁ : G₁) (δ₂ : G₂) (f₁ : G₁ → ℂ) (f₂ : G₂ → ℂ)
    (hK₁c : IsCompact (K₁ : Set G₁)) (hK₁o : IsOpen (K₁ : Set G₁))
    (hK₂c : IsCompact (K₂ : Set G₂)) (hK₂o : IsOpen (K₂ : Set G₂))
    (hf₁ : ∀ k ∈ K₁, ∀ y, f₁ (k⁻¹ * y * MonoidHom.id G₁ k) = f₁ y)
    (hf₂ : ∀ k ∈ K₂, ∀ y, f₂ (k⁻¹ * y * MonoidHom.id G₂ k) = f₂ y)
    (hv₁ : ∀ t ∈ twCent (MonoidHom.id G₁) δ₁, vol (twCent (MonoidHom.id G₁) δ₁ ⊓ K₁)
      ((twCent (MonoidHom.id G₁) δ₁ ⊓ K₁).map (MulAut.conj t).toMonoidHom) = 1)
    (hv₂ : ∀ t ∈ twCent (MonoidHom.id G₂) δ₂, vol (twCent (MonoidHom.id G₂) δ₂ ⊓ K₂)
      ((twCent (MonoidHom.id G₂) δ₂ ⊓ K₂).map (MulAut.conj t).toMonoidHom) = 1) :
    ∀ t ∈ twCent (MonoidHom.id (G₁ × G₂)) (δ₁, δ₂), ∀ k ∈ K₁.prod K₂, ∀ x,
      oTerm (MonoidHom.id (G₁ × G₂)) (K₁.prod K₂) (twCent (MonoidHom.id (G₁ × G₂)) (δ₁, δ₂) ⊓ K₁.prod K₂) (δ₁, δ₂)
          (fun w => f₁ w.1 * f₂ w.2) (t * x * k) =
        oTerm (MonoidHom.id (G₁ × G₂)) (K₁.prod K₂) (twCent (MonoidHom.id (G₁ × G₂)) (δ₁, δ₂) ⊓ K₁.prod K₂) (δ₁, δ₂)
          (fun w => f₁ w.1 * f₂ w.2) x := by
  intro t ht k hk x
  rw [← prodMap_id_eq] at ht ⊢
  rw [twCent_prod] at ht ⊢
  rw [Subgroup.mem_prod] at ht hk
  rw [show t * x * k = (t.1 * x.1 * k.1, t.2 * x.2 * k.2) from rfl, show x = (x.1, x.2) from rfl,
    oTerm_prod, oTerm_prod,
    oTerm_inv _ K₁ δ₁ f₁ hK₁c hK₁o hf₁ hv₁ ht.1 hk.1, oTerm_inv _ K₂ δ₂ f₂ hK₂c hK₂o hf₂ hv₂ ht.2 hk.2]

end Prod

theorem natDegree_minpoly_le (F L C : Type) [Field F] [Field L] [Algebra F L] [Ring C]
    [Algebra F C] [Algebra.IsCentral F C] [IsSimpleRing C] [FiniteDimensional F C] (n : ℕ) (hn : 0 < n)
    (ι : C →ₐ[F] Matrix (Fin n) (Fin n) L) (a : C) : (minpoly F a).natDegree ≤ n := by
  haveI : NeZero n := ⟨hn.ne'⟩
  let g : L ⊗[F] C →ₐ[L] Matrix (Fin n) (Fin n) L :=
    Algebra.TensorProduct.lift (Algebra.ofId L _) ι (fun l y ↦ Algebra.commute_algebraMap_left l _)
  haveI : IsSimpleRing (L ⊗[F] C) := GroundTheory.Brauer.isSimpleRing_tensorProduct_of_right
  have hg : Function.Injective g := GlobalTheory.CsaCharpoly.injective_of_isSimpleRing g.toRingHom
  have eg : g ((1 : L) ⊗ₜ a) = ι a := by
    simp only [g]; erw [Algebra.TensorProduct.lift_tmul]; simp
  have hyi : IsIntegral L ((1 : L) ⊗ₜ[F] a) := IsIntegral.of_finite L _
  have hmin : minpoly L (ι a) = minpoly L ((1 : L) ⊗ₜ[F] a) := by
    rw [← eg]; exact minpoly.algHom_eq g hg _
  have h1 := GlobalTheory.CsaCharpoly.natDegree_minpoly_le_one_tmul L a hyi
  rw [← hmin] at h1
  have h2 : (minpoly L (ι a)).natDegree ≤ (ι a).charpoly.natDegree :=
    Polynomial.natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly _) (Matrix.charpoly_monic _).ne_zero
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h2
  omega

theorem not_irreducible_map {F L : Type} [Field F] [Field L] (φ : F →+* L) (p : Polynomial F) (hp : p.Monic)
    (hirr : ¬ Irreducible p) : ¬ Irreducible (p.map φ) :=
  fun h => hirr (Polynomial.Monic.irreducible_of_irreducible_map φ p hp h)

theorem vol_conj_eq_one_of_separable (k : Type) [Field k] (n : ℕ) (γ : GL (Fin n) k) (K₀ : Subgroup (GL (Fin n) k))
    (hs : (γ : Matrix (Fin n) (Fin n) k).charpoly.Separable) :
    ∀ s ∈ twCent (MonoidHom.id _) γ, GlobalTheory.LKCount.vol (twCent (MonoidHom.id _) γ ⊓ K₀)
      ((twCent (MonoidHom.id _) γ ⊓ K₀).map (MulAut.conj s).toMonoidHom) = 1 := by
  intro s hs'
  have hs0 : s * γ = γ * s := hs'
  have hfix : ∀ c ∈ twCent (MonoidHom.id _) γ ⊓ K₀, (MulAut.conj s).toMonoidHom c = c := by
    intro c hc
    have hc0 : c * γ = γ * c := hc.1
    have := GlobalTheory.CentSep.centraliser_comm_of_separable k (Fin n) γ s c hs hs0 hc0
    show s * c * s⁻¹ = c
    rw [this, mul_inv_cancel_right]
  have hmap : (twCent (MonoidHom.id _) γ ⊓ K₀).map (MulAut.conj s).toMonoidHom = twCent (MonoidHom.id _) γ ⊓ K₀ := by
    ext c
    constructor
    · rintro ⟨c', hc', rfl⟩
      rw [hfix c' hc']; exact hc'
    · intro hc
      exact ⟨c, hc, hfix c hc⟩
  rw [hmap]
  simp [GlobalTheory.LKCount.vol, Subgroup.relIndex_self]

theorem orbK_eq_zero_of_split {A : Type} [Group A] (k : Type) [Field k] [TopologicalSpace k] [IsTopologicalRing k]
    [T2Space k] (n : ℕ) (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (e : A ≃* GL (Fin n) k × H) (K : Subgroup A) (K₀ : Subgroup (GL (Fin n) k)) (K'' : Subgroup H)
    (h0o : IsOpen (K₀ : Set (GL (Fin n) k))) (h0c : IsCompact (K₀ : Set (GL (Fin n) k)))
    (h1o : IsOpen (K'' : Set H)) (h1c : IsCompact (K'' : Set H)) (hmap : K.map e.toMonoidHom = K₀.prod K'')
    (f₀ : GL (Fin n) k → ℂ) (f'' : H → ℂ) (F : A → ℂ) (hF : ∀ h, F h = f₀ (e h).1 * f'' (e h).2)
    (hbi : ∀ c ∈ K₀, ∀ c' ∈ K₀, ∀ g, f₀ (c * g * c') = f₀ g) (hf'' : ∀ c ∈ K'', ∀ z, f'' (c⁻¹ * z * c) = f'' z)
    (δ : A) (hs : ((e δ).1 : Matrix (Fin n) (Fin n) k).charpoly.Separable)
    (hv : ∀ s ∈ twCent (MonoidHom.id H) (e δ).2, GlobalTheory.LKCount.vol (twCent (MonoidHom.id H) (e δ).2 ⊓ K'')
      ((twCent (MonoidHom.id H) (e δ).2 ⊓ K'').map (MulAut.conj s).toMonoidHom) = 1)
    (h0 : orbK (MonoidHom.id _) K₀ (e δ).1 f₀ = 0) : orbK (MonoidHom.id A) K δ F = 0 := by
  have hFe : (fun z => F (e.symm z)) = fun w : GL (Fin n) k × H => f₀ w.1 * f'' w.2 := by
    funext z; rw [hF, MulEquiv.apply_symm_apply]
  have hf₁ : ∀ c ∈ K₀, ∀ y, f₀ (c⁻¹ * y * MonoidHom.id _ c) = f₀ y :=
    fun c hc y => hbi _ (K₀.inv_mem hc) _ hc y
  have hv₁ := vol_conj_eq_one_of_separable k n (e δ).1 K₀ hs
  rw [orbK_congr_equiv e K δ F]
  · rw [hmap, hFe, ← prodMap_id_eq]
    have := orbK_prod (MonoidHom.id _) (MonoidHom.id H) K₀ K'' (e δ).1 (e δ).2 f₀ f'' continuous_id continuous_id
      h0c h0o h1c h1o hf₁ hf'' hv₁ hv
    rw [h0, zero_mul] at this
    exact this
  · rw [hmap, hFe]
    exact oTerm_prod_inv K₀ K'' (e δ).1 (e δ).2 f₀ f'' h0c h0o h1c h1o hf₁ hf'' hv₁ hv

theorem orbK_eq_zero_of_not_regIrr : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (k₀ : Type) [Field k₀] [ValuativeRel k₀] [TopologicalSpace k₀] [IsNonarchimedeanLocalField k₀] [MeasurableSpace k₀] [BorelSpace k₀] [Algebra G.F k₀] (ι₀ : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) k₀) (k₁ : Type) [Field k₁] [Algebra G.F k₁] (ι₁ : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) k₁) (H' : Type) [Group H'] [TopologicalSpace H'] [IsTopologicalGroup H'] [T2Space H'] (e : G.GAf × Gr G 1 ≃* GL (Fin G.n) k₀ × H') (π₁ : G.GAf × Gr G 1 →* GL (Fin G.n) k₁),
  (∀ (B : DForm G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) B.β x t) (y : GlobalTheory.LKCx.grp G B.β), (((e (B.embAt x t hx y)).1 : GL (Fin G.n) k₀) : Matrix (Fin G.n) (Fin G.n) k₀).charpoly = (ι₀ ((y.1.1 : G.Cˣ) : G.C)).charpoly ∧ ((π₁ (B.embAt x t hx y) : GL (Fin G.n) k₁) : Matrix (Fin G.n) (Fin G.n) k₁).charpoly = (ι₁ ((y.1.1 : G.Cˣ) : G.C)).charpoly) →
  ∀ (L : G.Level) (K' : Subgroup (Gr G 1)) (K₀ : Subgroup (GL (Fin G.n) k₀)) (K'' : Subgroup H'), IsOpen (K₀ : Set (GL (Fin G.n) k₀)) → IsCompact (K₀ : Set (GL (Fin G.n) k₀)) → IsOpen (K'' : Set H') → IsCompact (K'' : Set H') →
  (L.K.toSubgroup.prod K').map e.toMonoidHom = K₀.prod K'' →
  ∀ (f₀ : GL (Fin G.n) k₀ → ℂ) (f'' : H' → ℂ) (f : G.GAf → ℂ) (f' : Gr G 1 → ℂ),
  (∀ h : G.GAf × Gr G 1, f h.1 * f' h.2 = f₀ (e h).1 * f'' (e h).2) →
  (∀ h : G.GAf × Gr G 1, f h.1 * f' h.2 ≠ 0 → ((π₁ h : GL (Fin G.n) k₁) : Matrix (Fin G.n) (Fin G.n) k₁).charpoly.Separable) →
  IsLocallyConstant f₀ → HasCompactSupport f₀ → (∀ (a b : ℕ) (ε : Fin G.n ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → k₀)), μ.IsAddHaarMeasure →
    ∀ u : (Fin a → Fin b → k₀) → GL (Fin G.n) k₀,
      (∀ X, (u X : Matrix (Fin G.n) (Fin G.n) k₀) = Matrix.reindex ε.symm ε.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ g h : GL (Fin G.n) k₀, ∫ X, f₀ (g * (h⁻¹ * u X * h)) ∂μ = 0) →
  (∀ k ∈ K₀, ∀ k' ∈ K₀, ∀ g, f₀ (k * g * k') = f₀ g) → (∀ k ∈ K'', ∀ z, f'' (k⁻¹ * z * k) = f'' z) →
  (∀ (B : DForm G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) B.β x t) (y : GlobalTheory.LKCx.grp G B.β), (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).natDegree = G.n → (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).Separable → ∀ s ∈ GlobalTheory.BCT.twCent (MonoidHom.id H') (e (B.embAt x t hx y)).2, GlobalTheory.LKCount.vol (GlobalTheory.BCT.twCent (MonoidHom.id H') (e (B.embAt x t hx y)).2 ⊓ K'') ((GlobalTheory.BCT.twCent (MonoidHom.id H') (e (B.embAt x t hx y)).2 ⊓ K'').map (MulAut.conj s).toMonoidHom) = 1) →
  ∀ (B : DForm G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) B.β x t) (y : GlobalTheory.LKCx.grp G B.β), ¬ RegIrr G ((y.1.1 : G.Cˣ) : G.C) →
    GlobalTheory.LKCount.orbK (MonoidHom.id _) (L.K.toSubgroup.prod K') (B.embAt x t hx y) (fun h => f h.1 * f' h.2) = 0 := by
  intro p _ G k₀ _ _ _ _ _ _ _ ι₀ k₁ _ _ ι₁ H' _ _ _ _ e π₁ hc L K' K₀ K'' h0o h0c h1o h1c hmap f₀ f'' f f' hprod hsep
    hlc hcs hcusp hbi hf'' hvol B x t hx y hy
  obtain ⟨hc0, hc1⟩ := hc B x t hx y
  by_cases hs1 : ((π₁ (B.embAt x t hx y) : GL (Fin G.n) k₁) : Matrix (Fin G.n) (Fin G.n) k₁).charpoly.Separable
  swap
  · exact GlobalTheory.orbK_eq_zero_of_charpoly_not_separable _ k₁ G.n π₁ _ _ _ hsep hs1
  rw [hc1] at hs1
  have hns := GlobalTheory.SepCharpoly.not_separable_charpoly G.F k₁ G.C G.n ι₁ ((y.1.1 : G.Cˣ) : G.C)
  have hle := natDegree_minpoly_le G.F k₁ G.C G.n G.n_pos ι₁ ((y.1.1 : G.Cˣ) : G.C)
  have hdeg : (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).natDegree = G.n := by
    by_contra h
    exact hns (Or.inl (lt_of_le_of_ne hle h)) hs1
  have hsm : (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)).Separable := by
    by_contra h
    exact hns (Or.inr ⟨hdeg, h⟩) hs1
  have hirr : ¬ Irreducible (minpoly G.F ((y.1.1 : G.Cˣ) : G.C)) := fun h => hy ⟨hdeg, hsm, h⟩
  rw [GlobalTheory.charpoly_algHom_eq_map_minpoly G.F k₀ G.C G.n G.rankC ι₀ _ hdeg] at hc0
  have hs0 : (((e (B.embAt x t hx y)).1 : GL (Fin G.n) k₀) : Matrix (Fin G.n) (Fin G.n) k₀).charpoly.Separable := by
    rw [hc0]; exact hsm.map
  have hi0 : ¬ Irreducible
      (((e (B.embAt x t hx y)).1 : GL (Fin G.n) k₀) : Matrix (Fin G.n) (Fin G.n) k₀).charpoly := by
    rw [hc0]
    exact not_irreducible_map _ _ (minpoly.monic (IsIntegral.of_finite G.F _)) hirr
  haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
  have h0 := GlobalTheory.LKCount.orbK_eq_zero_of_cusp k₀ (Fin G.n) f₀ hlc hcs hcusp _ hs0 hi0 K₀ h0o h0c hbi
  exact orbK_eq_zero_of_split k₀ G.n H' e _ K₀ K'' h0o h0c h1o h1c hmap f₀ f'' _ hprod hbi hf'' _ hs0
    (hvol B x t hx y hdeg hsm) h0

end GlobalTheory.VanishNonEll
