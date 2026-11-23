import Formalism.WachLatticeTwists.HodgeTateChains.ProductEqXiPowerSmulOne
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.UnitCongruenceGivesPerturbationStatement

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

open Matrix

theorem hypWComm : StatHypWComm := by
  intro ℓ _ As AA WC _ _ _ _ jA ι φ Gg _ H act r ρ πs ξ M0 h0 W hfix hinj h hh h' hh'
  have e1 := W.fixH h hh
  have e2 := W.fixH h' hh'
  have e3 := W.fixH (h * h') (H.mul_mem hh hh')
  generalize hR : ((ρ h : Matrix (Fin r) (Fin r) ℤ_[ℓ]).map (algebraMap ℤ_[ℓ] WC)) = R at *
  generalize hR' : ((ρ h' : Matrix (Fin r) (Fin r) ℤ_[ℓ]).map (algebraMap ℤ_[ℓ] WC)) = R' at *
  have e6 : ((ρ (h * h') : Matrix (Fin r) (Fin r) ℤ_[ℓ]).map (algebraMap ℤ_[ℓ] WC)) = R * R' := by
    rw [map_mul, Units.val_mul, Matrix.map_mul, hR, hR']
  have e4 : (W.Xx.map (act h')).map (act h) * R' = W.Xx.map (act h) := by
    have h1 : (W.Xx.map (act h') * R').map (act h) = W.Xx.map (act h) := by rw [e2]
    rw [← h1]
    ext i j
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hR']
    simp [Matrix.map_apply, hfix]
  have e5 : W.Xx.map (act (h * h')) = (W.Xx.map (act h')).map (act h) := by
    ext i j; simp [Matrix.map_apply, map_mul]
  generalize (W.Xx.map (act h')).map (act h) = Y at *
  have k1 : Y * (R' * R) = W.Xx := by rw [← Matrix.mul_assoc, e4, e1]
  have k2 : Y * (R * R') = W.Xx := by rw [← e6, ← e5]; exact e3
  have hYl : ((R' * R) * W.Xi) * Y = 1 := by
    have : Y * ((R' * R) * W.Xi) = 1 := by rw [← Matrix.mul_assoc, k1, W.inv1]
    exact mul_eq_one_comm.mp this
  have k3 : R' * R = R * R' := by
    calc R' * R = (((R' * R) * W.Xi) * Y) * (R' * R) := by rw [hYl, Matrix.one_mul]
      _ = ((R' * R) * W.Xi) * (Y * (R' * R)) := by simp only [Matrix.mul_assoc]
      _ = ((R' * R) * W.Xi) * (Y * (R * R')) := by rw [k1, k2]
      _ = (((R' * R) * W.Xi) * Y) * (R * R') := by simp only [Matrix.mul_assoc]
      _ = R * R' := by rw [hYl, Matrix.one_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  have : ((ρ h : Matrix (Fin r) (Fin r) ℤ_[ℓ]) * (ρ h' : Matrix (Fin r) (Fin r) ℤ_[ℓ])).map
        (algebraMap ℤ_[ℓ] WC)
      = ((ρ h' : Matrix (Fin r) (Fin r) ℤ_[ℓ]) * (ρ h : Matrix (Fin r) (Fin r) ℤ_[ℓ])).map
        (algebraMap ℤ_[ℓ] WC) := by
    rw [Matrix.map_mul, Matrix.map_mul, hR, hR', k3]
  exact Matrix.map_injective hinj this

theorem wSandwich' : StatWSandwich' := by
  intro ℓ _ As AA WC OC _ _ _ _ _ jA ι φ Gg _ H act GK _ inc r ρ πs ξ x M0 h0 W ϑ c hL hinj hx hξ hc
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨⟨A, hA⟩, ⟨A', hA'⟩⟩ := sandwichAA AA WC ι φ (jA x) (jA ξ) r M0 h0 W.Xx W.Xi W.P
    (W.P1.map jA) (W.Q1.map jA) hL hx hξ W.inv1 W.inv2 W.W1 W.map_eq_xi_power_smul (by
      rw [← Matrix.map_mul, W.product_eq_xi_power_smul_one, Matrix.map_smul' jA _ _ (map_mul jA),
        Matrix.map_one jA (map_zero jA) (map_one jA), map_pow])
  have hminj : Function.Injective (fun M : Matrix (Fin r) (Fin r) AA => M.map ι) := by
    intro M M' h
    ext i j
    exact hinj (congrFun (congrFun h i) j)
  have hscal : (((jA x) ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) AA)).map ι
      = (ι (jA x)) ^ (M0 + h0) • (1 : Matrix (Fin r) (Fin r) WC) := by
    rw [Matrix.map_smul' ι _ _ (map_mul ι), Matrix.map_one ι (map_zero ι) (map_one ι), map_pow]
  have h1 : A * A' = ((jA x) ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) AA) := by
    apply hminj
    show (A * A').map ι = (((jA x) ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) AA)).map ι
    rw [Matrix.map_mul, hA, hA', hscal, Matrix.smul_mul, Matrix.mul_smul, W.inv1, smul_smul, ← pow_add]
  have h2 : A' * A = ((jA x) ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) AA) := by
    apply hminj
    show (A' * A).map ι = (((jA x) ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) AA)).map ι
    rw [Matrix.map_mul, hA, hA', hscal, Matrix.smul_mul, Matrix.mul_smul, W.inv2, smul_smul, ← pow_add,
      add_comm]
  obtain ⟨Y', hY1, hY2⟩ := sandwichOC ℓ hℓ AA OC ϑ (jA x) c r M0 h0 A A' hc h1 h2
  exact ⟨A, Y', hA, hY1, hY2⟩

lemma mapmap_inj {As AA WC : Type} [CommRing As] [CommRing AA] [CommRing WC] (jA : As →+* AA)
    (ι : AA →+* WC) (hinj : Function.Injective (fun a : As => ι (jA a))) {r : ℕ}
    {M M' : Matrix (Fin r) (Fin r) As} (h : (M.map jA).map ι = (M'.map jA).map ι) : M = M' := by
  ext i j
  exact hinj (congrFun (congrFun h i) j)

lemma mapmap_one {As AA WC : Type} [CommRing As] [CommRing AA] [CommRing WC] (jA : As →+* AA)
    (ι : AA →+* WC) {r : ℕ} : (((1 : Matrix (Fin r) (Fin r) As)).map jA).map ι = 1 := by
  rw [Matrix.map_one jA (map_zero jA) (map_one jA), Matrix.map_one ι (map_zero ι) (map_one ι)]

lemma cancel_right {WC : Type} [CommRing WC] {r : ℕ} {Xx Xi A B : Matrix (Fin r) (Fin r) WC}
    (h1 : Xx * Xi = 1) (h : A * Xx = B * Xx) : A = B := by
  calc A = A * (Xx * Xi) := by rw [h1, Matrix.mul_one]
    _ = B * (Xx * Xi) := by rw [← Matrix.mul_assoc, h, Matrix.mul_assoc]
    _ = B := by rw [h1, Matrix.mul_one]

theorem wFix : StatWFix := by
  intro ℓ _ As AA WC _ _ _ _ jA ι φ Gg _ H act GK _ inc r ρ πs ξ M0 h0 W hinj h hh
  apply mapmap_inj jA ι hinj
  rw [mapmap_one]
  apply cancel_right W.inv1
  rw [Matrix.one_mul, ← W.W2 h, W.fixH h hh]

theorem wCocycle : StatWCocycle := by
  intro ℓ _ As AA WC _ _ _ _ jA ι φ Gg _ H act GK _ inc r ρ πs ξ M0 h0 W hfix
  constructor
  · apply cancel_right W.inv1
    rw [Matrix.one_mul, ← W.W2 1]
    have e1 : W.Xx.map (act 1) = W.Xx := by ext i j; simp
    have e2 : ((ρ (inc 1) : Matrix (Fin r) (Fin r) ℤ_[ℓ])ᵀ.map (algebraMap ℤ_[ℓ] WC)) = 1 := by
      rw [map_one, map_one, Units.val_one, Matrix.transpose_one,
        Matrix.map_one _ (map_zero _) (map_one _)]
    rw [e1, e2, Matrix.mul_one]
  · intro g g'
    apply cancel_right W.inv1
    rw [← W.W2 (g * g')]
    have e1 : W.Xx.map (act (g * g')) = (W.Xx.map (act g')).map (act g) := by
      ext i j; simp [Matrix.map_apply, map_mul]
    have e2 : ((ρ (inc (g * g')) : Matrix (Fin r) (Fin r) ℤ_[ℓ])ᵀ.map (algebraMap ℤ_[ℓ] WC))
        = ((ρ (inc g') : Matrix (Fin r) (Fin r) ℤ_[ℓ])ᵀ.map (algebraMap ℤ_[ℓ] WC))
          * ((ρ (inc g) : Matrix (Fin r) (Fin r) ℤ_[ℓ])ᵀ.map (algebraMap ℤ_[ℓ] WC)) := by
      rw [map_mul, map_mul, Units.val_mul, Matrix.transpose_mul, Matrix.map_mul]
    have e3 : (((ρ (inc g') : Matrix (Fin r) (Fin r) ℤ_[ℓ])ᵀ.map (algebraMap ℤ_[ℓ] WC))).map (act g)
        = ((ρ (inc g') : Matrix (Fin r) (Fin r) ℤ_[ℓ])ᵀ.map (algebraMap ℤ_[ℓ] WC)) := by
      ext i j; simp [Matrix.map_apply, hfix]
    have e4 : (W.Xx.map (act g')).map (act g)
        * ((ρ (inc g') : Matrix (Fin r) (Fin r) ℤ_[ℓ])ᵀ.map (algebraMap ℤ_[ℓ] WC))
        = (((W.Gm g').map jA).map ι).map (act g) * W.Xx.map (act g) := by
      have := congrArg (fun M : Matrix (Fin r) (Fin r) WC => M.map (act g)) (W.W2 g')
      rw [Matrix.map_mul, Matrix.map_mul, e3] at this
      exact this
    rw [e1, e2, ← Matrix.mul_assoc, e4, Matrix.mul_assoc, W.W2 g, Matrix.mul_assoc]

theorem wGam : StatWGam := by
  intro ℓ _ As AA WC _ _ _ _ jA ι φ Gg _ H act GK _ inc r ρ πs ξ M0 h0 W γ σ hfix hinj hσ k i
  obtain ⟨c1, c2⟩ := wCocycle ℓ As AA WC jA ι φ Gg H act GK inc r ρ πs ξ M0 h0 W hfix
  induction k with
  | zero =>
    have h1 : W.Gm 1 = 1 := by
      apply mapmap_inj jA ι hinj
      rw [c1, mapmap_one]
    rw [pow_zero, h1, Function.iterate_zero, id]
    ext j
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  | succ k ih =>
    have h1 : W.Gm (γ ^ (k + 1)) = (W.Gm (γ ^ k)).map σ * W.Gm γ := by
      apply mapmap_inj jA ι hinj
      rw [pow_succ', c2, Matrix.map_mul, Matrix.map_mul]
      congr 1
      ext a b
      simp [Matrix.map_apply, hσ]
    rw [Function.iterate_succ_apply', ih, h1]
    ext j
    simp [gamN, Matrix.vecMul, dotProduct, Matrix.mul_apply]

theorem wUm : StatWUm := by
  intro ℓ _ As AA WC R _ _ _ _ _ jA ι φ Gg _ H act GK _ inc r ρ πs ξ M0 h0 W γ σ ϑ z ϖ ϖ' s n hfix hinj hσ
    h1 h2 h3 h4 h5 h6 h7 i j
  have := w3Um ℓ Fact.out As R σ πs ϑ z ϖ ϖ' r s n (W.Gm γ) h1 h2 (W.W3 γ) h3 h4 h5 h6 h7 i j
  rw [wGam ℓ As AA WC jA ι φ Gg H act GK inc r ρ πs ξ M0 h0 W γ σ hfix hinj hσ] at this
  rw [Matrix.sub_apply]
  exact this

theorem wEnd : StatWEnd := by
  intro ℓ _ As AA WC OC _ _ _ _ _ _ jA ι φ Gg _ H act GK _ inc r ρ πs ξ x M0 h0 W ϑ A hinj hal hA E hE
  obtain ⟨E', hE'⟩ := W.W4 E hE
  refine ⟨E', ?_⟩
  have hm : (Eᵀ.map (algebraMap ℤ_[ℓ] AA)).map ι = Eᵀ.map (algebraMap ℤ_[ℓ] WC) := by
    ext a b; simp [Matrix.map_apply, hal]
  have key : A * Eᵀ.map (algebraMap ℤ_[ℓ] AA) = E'.map jA * A := by
    have hminj : Function.Injective (fun M : Matrix (Fin r) (Fin r) AA => M.map ι) := by
      intro M M' h
      ext a b
      exact hinj (congrFun (congrFun h a) b)
    apply hminj
    show (A * Eᵀ.map (algebraMap ℤ_[ℓ] AA)).map ι = (E'.map jA * A).map ι
    rw [Matrix.map_mul, Matrix.map_mul, hm, hA, Matrix.smul_mul, hE', Matrix.mul_smul]
  rw [← Matrix.map_mul, key, Matrix.map_mul]

theorem torsAll (ℓ : ℕ) [Fact ℓ.Prime] (w : ℤ_[ℓ]ˣ) (m : ℕ) (hm : 1 ≤ m) (h2 : ℓ = 2 → 2 ≤ m)
    (hw : PadicInt.valuation ((w : ℤ_[ℓ]) - 1) = m) (U : Finset ℤ) (a : ℤ) (D : FreeData ℓ)
    (hD : D.Inputs) (hP : ∀ i, (D.piece i).Inputs w U (a + i))
    (hk : ∀ i k j, i < k → k < j → ∀ x, D.i1 i k j x = 0 → ∃ t : ℕ, ((ℓ : ℤ_[ℓ]) ^ t) • x = 0) :
    ∀ n i j, j = i + n + 1 →
      TorsKilled ℓ (D.H1 i j) (∑ x ∈ Finset.Ico i j, (2 + max 1 (rI ℓ m U (a + x)))) := by
  intro n
  induction n with
  | zero =>
    intro i j hj
    subst hj
    have := piece ℓ w m hm h2 hw U (a + i) (D.H1 i (i + 1)) (D.piece i) (hP i)
    simpa using this
  | succ n ih =>
    intro i j hj x hx
    obtain ⟨t, ht⟩ := hx
    have hij : i < j := by omega
    obtain ⟨_, hex, _, _, _⟩ := hD i (i + 1) j (by omega) (by omega)
    have h0 := piece ℓ w m hm h2 hw U (a + i) (D.H1 i (i + 1)) (D.piece i) (hP i)
      (D.p1 i (i + 1) j x) ⟨t, by rw [← map_smul, ht, map_zero]⟩
    rw [← map_smul] at h0
    obtain ⟨y', hy'⟩ := (hex _).1 h0
    obtain ⟨t', ht'⟩ := hk i (i + 1) j (by omega) (by omega) (((ℓ : ℤ_[ℓ]) ^ t) • y') (by
      rw [map_smul, hy', smul_comm, ht, smul_zero])
    have h1 := ih (i + 1) j (by omega) y' ⟨t' + t, by rw [pow_add, mul_smul, ht']⟩
    rw [Finset.sum_eq_sum_Ico_succ_bot hij, add_comm, pow_add, mul_smul, ← hy', ← map_smul, h1,
      map_zero]

theorem freeGm' : StatFreeGm' := by
  intro ℓ _ w m hm h2 hw U a D hD hP hc hex
  refine freeGm ℓ w m hm h2 hw U a D hD hP hc fun i j hij => ?_
  refine torsAll ℓ w m hm h2 hw U a D hD hP (fun i k j hik hkj x hx => ?_) (j - i - 1) i j (by omega)
  obtain ⟨z, rfl⟩ := (hex i k j hik hkj x).1 hx
  exact (hD i k j hik hkj).2.2.2.2 z

theorem freeKTop : StatFreeKTop := by
  intro ℓ _ InvariantsKilledOverCyclotomic H1K H1m H0m H0KQ H1KQ H0mQ H1mQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cupK b0 b1 cupKQ resQ
    res cup a0 a1 r0 cupQ al h1 h2 h3 h4 hinj hsur htf hker hpb hF y
  obtain ⟨z, hz⟩ := hsur (b1 y)
  obtain ⟨zm, hzm⟩ := freeK ℓ H1K H1m H0m H0KQ H0mQ H1mQ res cup a0 a1 r0 cupQ al h1 hinj htf hF y z
    (by rw [h3, ← hz, h4])
  obtain ⟨zK, hzK⟩ := hpb (((ℓ : ℤ_[ℓ]) ^ al) • z) zm (by rw [hzm, map_smul])
  obtain ⟨t, ht⟩ := hker (((ℓ : ℤ_[ℓ]) ^ al) • y - cupK zK) (by
    rw [map_sub, map_smul, h2, hzK, map_smul, hz, sub_self])
  exact ⟨zK, t, ht⟩

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
