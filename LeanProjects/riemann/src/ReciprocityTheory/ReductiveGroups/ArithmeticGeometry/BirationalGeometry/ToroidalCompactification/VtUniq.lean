import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullFEPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U]

theorem cubN_right {θ : A → A → A → U} (h : IsCub θ) {k : ℕ} {x : A} (hx : x ^ k = 1) (z y : A) :
    cubN θ k 1 x (z * y) * θ x z y ^ k = cubN θ k 1 x z * cubN θ k 1 x y := by
  have cyc : ∀ p q r, θ r p q = θ p q r := fun p q r => (h.s01 r p q).trans (h.s12 p r q)
  have key : ∀ a, θ a x (z * y) * θ x z y = θ a x z * θ a x y * (θ (a * x) z y * (θ a z y)⁻¹) := by
    intro a
    have c1 := h.coc x z y a
    have c2 := h.coc a x z y
    rw [← cyc x z a, ← cyc (x * z) y a, ← cyc x (z * y) a, ← cyc z y a] at c1
    rw [← _root_.mul_assoc, eq_mul_inv_iff_mul_eq]
    calc θ a x (z * y) * θ x z y * θ a z y = θ a x (z * y) * θ a z y * θ x z y := mul_right_comm _ _ _
      _ = θ a (x * z) y * θ a x z * θ x z y := by rw [← c1]
      _ = θ a x z * (θ a (x * z) y * θ x z y) := by rw [mul_comm (θ a (x * z) y) (θ a x z), _root_.mul_assoc]
      _ = θ a x z * (θ (a * x) z y * θ a x y) := by rw [← c2]
      _ = θ a x z * θ a x y * θ (a * x) z y := by rw [mul_comm (θ (a * x) z y) (θ a x y), _root_.mul_assoc]
  have htel : ∏ i ∈ Finset.range k, (θ (x ^ i * x) z y * (θ (x ^ i) z y)⁻¹) = 1 := by
    have := Finset.prod_range_div (fun i => θ (x ^ i) z y) k
    simp only [pow_succ, div_eq_mul_inv] at this
    rw [this, hx, pow_zero, mul_inv_cancel]
  have hG : θ x z y ^ k = ∏ _i ∈ Finset.range k, θ x z y := by simp
  unfold cubN
  simp only [_root_.one_mul]
  rw [hG, ← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun i _ => key (x ^ i)), Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, htel, _root_.mul_one]

theorem lift_const {k : ℕ} (hk : Odd k) {t d : A} (ht : t ^ k = 1) (hd : d ^ k = 1) (φ' φ β ν' ν κ : A → U) (c e : U)
    (hga : ∀ y, φ (y * d) * β (y * d * t) * β y = φ y * β (y * t) * β (y * d))
    (hc : ∀ y, φ' y * β (y * (t * d)) = c * (φ y * β (y * t)))
    (p' : ∏ j ∈ Finset.range k, φ' ((t * d) ^ j) = 1) (p : ∏ j ∈ Finset.range k, φ (t ^ j) = 1)
    (s' : φ' (t * d)⁻¹ * ν' 1 * (φ' 1 * (ν' (t * d)⁻¹)⁻¹) = 1) (s : φ t⁻¹ * ν 1 * (φ 1 * (ν t⁻¹)⁻¹) = 1)
    (hν : ∀ y, ν' y = e * ν y) (hκ : ∀ y, β y = β y⁻¹ * ν y * κ y) (hκd : κ (t * d)⁻¹ = κ t⁻¹) : c = 1 := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : A → U, ∀ y, ψ y = φ y * (β (y * t) / β y) := ⟨_, fun _ => rfl⟩
  have hψd : ∀ y, ψ (y * d) = ψ y := by
    intro y
    rw [hψ, hψ, ← mul_div_assoc, ← mul_div_assoc, div_eq_div_iff_mul_eq_mul]
    exact hga y
  have hψinv : ∀ y, ψ (y * d⁻¹) = ψ y := by
    intro y
    have := hψd (y * d⁻¹)
    rw [inv_mul_cancel_right] at this
    exact this.symm
  have hψpow : ∀ (j : ℕ) y, ψ (y * d ^ j) = ψ y := by
    intro j
    induction j with
    | zero => intro y; rw [pow_zero, _root_.mul_one]
    | succ j ih => intro y; rw [pow_succ, ← _root_.mul_assoc, hψd, ih]
  have hφ' : ∀ y, φ' y = c * (ψ y * β y) / β (y * (t * d)) := by
    intro y
    rw [eq_div_iff_mul_eq', hc, hψ, _root_.mul_assoc (φ y), div_mul_cancel]
  have hφ : ∀ y, φ y = ψ y * β y / β (y * t) := by
    intro y
    rw [hψ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div]
    abel
  have hψu : ∀ j : ℕ, ψ ((t * d) ^ j) = ψ (t ^ j) := by
    intro j
    rw [mul_pow, hψpow]
  have hu : (t * d) ^ k = 1 := by rw [mul_pow, ht, hd, _root_.one_mul]
  have hterm : ∀ j : ℕ, φ' ((t * d) ^ j) = (c * ψ (t ^ j)) * (β ((t * d) ^ j) / β ((t * d) ^ (j + 1))) := by
    intro j
    rw [hφ', hψu, pow_succ]
    simp only [div_eq_mul_inv, _root_.mul_assoc]
  have hψ1 : ∏ j ∈ Finset.range k, ψ (t ^ j) = 1 := by
    simp only [hψ, Finset.prod_mul_distrib, p, _root_.one_mul]
    simp only [← pow_succ]
    rw [Finset.prod_range_div (fun j => β (t ^ j)), ht, pow_zero, div_self']
  have hck : c ^ k = 1 := by
    have h1 := p'
    rw [Finset.prod_congr rfl (fun j _ => hterm j), Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_range, hψ1, _root_.mul_one] at h1
    have htel : ∏ j ∈ Finset.range k, (β ((t * d) ^ j) / β ((t * d) ^ (j + 1))) = 1 := by
      rw [Finset.prod_range_div' (fun j => β ((t * d) ^ j)), hu, pow_zero, div_self']
    rwa [htel, _root_.mul_one] at h1
  have hβu : β (t * d)⁻¹ = β (t * d) * ν (t * d)⁻¹ * κ t⁻¹ := by
    conv_lhs => rw [hκ]
    rw [inv_inv, hκd]
  have hβt : β t⁻¹ = β t * ν t⁻¹ * κ t⁻¹ := by
    conv_lhs => rw [hκ]
    rw [inv_inv]
  have hψtd : ψ (t * d)⁻¹ = ψ t⁻¹ := by rw [mul_inv, hψinv]
  have key : ∀ (c ψa ψb βu βt β1 νu νt ν1 κa e : U),
      c * (ψa * (βu * νu * κa)) / β1 * (e * ν1) * (c * (ψb * β1) / βu * (e * νu)⁻¹) =
        c ^ 2 * (ψa * (βt * νt * κa) / β1 * ν1 * (ψb * β1 / βt * νt⁻¹)) := by
    intros
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_inv, ofMul_pow]
    abel
  have s2 := s'
  rw [hφ' (t * d)⁻¹, hφ' 1, hν, hν, inv_mul_cancel, _root_.one_mul, hψtd, hβu] at s2
  have s1 := s
  rw [hφ t⁻¹, hφ 1, inv_mul_cancel, _root_.one_mul, hβt] at s1
  rw [key, s1, _root_.mul_one] at s2
  obtain ⟨m, rfl⟩ := hk
  rw [pow_succ, pow_mul, s2, one_pow, _root_.one_mul] at hck
  exact hck

end Alg

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem surj_fst (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (T : Over S) : Function.Surjective (fst T A).left.appTop.hom := by
  have e : (fst T A).left = (pullbackSymmetry T.hom A.hom).hom ≫ (snd A T).left := (pullbackSymmetry_hom_comp_snd _ _).symm
  have : IsIso (pullbackSymmetry T.hom A.hom).hom.appTop := inferInstanceAs (IsIso ((pullbackSymmetry T.hom A.hom).hom.app ⊤))
  rw [e]
  exact surj_comp (ConcreteCategory.bijective_of_isIso (pullbackSymmetry T.hom A.hom).hom.appTop).2 (surj_snd hG hA T)

theorem ratio_const (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) {T : Over S} {K K' : Type}
    [Fintype K] [Fintype K'] {φ : K → ((T ⊗ A).left ⟶ A.left)} {ε : K → ℤ} {φ' : K' → ((T ⊗ A).left ⟶ A.left)} {ε' : K' → ℤ}
    (hF : FormEq φ' ε' φ ε) {u : LB.Gen (LB.LinComb L φ ε)} {u' : LB.Gen (LB.LinComb L φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen)
    {T' : Over S} (σ : T' ⟶ T) (y : T' ⟶ A) {z : T'.left} {J} (hJ : Good L z J) :
    val u (lift σ y).left z J * val u' (lift σ 1).left z J = val u' (lift σ y).left z J * val u (lift σ 1).left z J := by
  let n : T ⊗ A ⟶ T ⊗ A := lift (fst T A) 1
  have hn : ∀ {T' : Over S} (σ : T' ⟶ T) (y : T' ⟶ A), (lift σ y).left ≫ n.left = (lift σ 1).left := fun σ y => by
    rw [← Over.comp_left, comp_lift, lift_fst, MonObj.comp_one]
  have key := gen_unique' hL (fun U _ h => (prod_sum₂ (K := K') (K' := K) (U := U) _ (hF U h)
      (c' := ∏ k, h (n.left ≫ φ k) ^ ε k) rfl).trans (prod_sum₂ (K := K) (K' := K') (U := U) _ rfl
      (hF U fun q => h (n.left ≫ q))).symm) (fst T A).left (lift (𝟙 T) (1 : T ⟶ A)).left
    (congrArg (fun q => q.left) (lift_fst _ _ : lift (𝟙 T) (1 : T ⟶ A) ≫ _ = _)) (surj_fst hG hA T)
    (mulGen_isGen _ _ _ _ _ _ _ hu (pullGen_isGen _ _ _ _ hu' n.left))
    (mulGen_isGen _ _ _ _ _ _ _ hu' (pullGen_isGen _ _ _ _ hu n.left)) (fun w I hI => by
      rw [val_mul hI, val_mul hI, val_pull hI, val_pull hI, hn, mul_comm]) _ (lift σ y).left z J hJ
  rwa [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, hn] at key

theorem prod_two {T T' : Over S} (ρ : T' ⟶ T) (a b : T ⟶ A) (m n : ℤ) {U : Type} [CommGroup U] (h : (T'.left ⟶ A.left) → U) :
    ∏ i, h (ρ.left ≫ (![a.left, b.left] : Fin 2 → _) i) ^ (![m, n] : Fin 2 → ℤ) i = h (ρ ≫ a).left ^ m * h (ρ ≫ b).left ^ n := by
  simp [Fin.prod_univ_two]

theorem translPt_eq {T : Over S} (x : T ⟶ A) : translPt A x = (fst T A ≫ x) * snd T A := rfl

theorem lift_transl {T T' : Over S} (σ : T' ⟶ T) (y : T' ⟶ A) (x : T ⟶ A) :
    lift σ y ≫ translT A x = lift σ ((σ ≫ x) * y) := by
  simp only [translT, translPt_eq, comp_lift, lift_fst, lift_fst_assoc, lift_snd, comp_mul]

variable [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L)

theorem val_theta (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {T : Over S} {k : ℕ} {x : T ⟶ A} (hx : x ^ k = 1) {K : Type}
    [Fintype K] {φ : K → ((T ⊗ A).left ⟶ A.left)} {ε : K → ℤ} (u : LB.Gen (LB.LinComb L.L φ ε)) (hu : u.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (h : ((T ⊗ A).left ⟶ A.left) → U), ∏ i, h (φ i) ^ ε i =
      h (snd T A).left ^ k * (h ((fst T A ≫ x) * snd T A).left ^ k)⁻¹)
    {T' : Over S} (σ : T' ⟶ T) (y : T' ⟶ A) {z : T'.left} {J} (hJ : Good L.L z J) :
    val u (lift σ y).left z J = val u (lift σ 1).left z J * cubN (cubV c z J) k 1 (σ ≫ x) y := by
  have C : IsCub (cubV c z J) := isCub_cubV c hJ
  obtain ⟨t, ht, vt⟩ := exists_cubN c (1 : T ⊗ A ⟶ A) (fst T A ≫ x) (snd T A) k
  let n : T ⊗ A ⟶ T ⊗ A := lift (fst T A) 1
  have hn : ∀ y : T' ⟶ A, (lift σ y).left ≫ n.left = (lift σ 1).left := fun y => by
    rw [← Over.comp_left, comp_lift, lift_fst, MonObj.comp_one]
  have vt' : ∀ y : T' ⟶ A, val t (lift σ y).left z J = cubN (cubV c z J) k 1 (σ ≫ x) y := fun y => by
    rw [vt _ _ z J hJ, MonObj.comp_one, lift_fst_assoc, lift_snd]
  have key := ratio_const hG hA L.isLB (fun U _ h => by
      have e₁ : n ≫ snd T A = 1 := lift_snd _ _
      have e₂ : n ≫ ((fst T A ≫ x) * snd T A) = fst T A ≫ x := by
        rw [MonObj.comp_mul, lift_fst_assoc, e₁, _root_.mul_one]
      have p := hF U fun q => h (n.left ≫ q)
      rw [← Over.comp_left, ← Over.comp_left, e₁, e₂] at p
      refine (prod_sum₂ (K := K) (K' := Fin 8) (U := U) _ p (Fin.prod_univ_eight _)).trans (Eq.trans ?_ (hF U h).symm)
      simp only [Sum.elim_inr, Matrix.cons_val]
      rw [← MonObj.comp_pow, hx, MonObj.comp_one, _root_.one_mul (1 : T ⊗ A ⟶ A), _root_.one_mul (snd T A)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module) hu (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hu n.left) ht) σ y hJ
  rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, hn, hn, vt', vt', C.N_one, _root_.mul_one] at key
  exact mul_right_cancel key

theorem ros_pow' (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (u : LB.Gen (LB.LinComb L.L (rosatiφ A f g) rosatiε)) (hu : u.IsGen)
    (n : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ u (zero2 A)) (LB.oneGen L.L)) {T : Over S} {z : T.left} {J}
    (hJ : Good L.L z J) {k : ℕ} {x m : T ⟶ A} (hx : x ^ k = 1) (hm : m ^ k = 1) (hf : m ≫ f = 1) :
    cubN (cubV c z J) k 1 m (x ≫ g) = cubN (cubV c z J) k 1 (x ≫ g) m := by
  have C : IsCub (cubV c z J) := isCub_cubV c hJ
  have ra := fun x x' y => ros_add c hG hA f g u hu n hJ x x' y
  have u₁ : ∀ w, val₂ u z J (1 : T ⟶ A) w = 1 := fun w => by
    have e := (ra 1 1 w).1
    rw [_root_.mul_one, MonObj.one_comp f, C.face, C.face, _root_.mul_one, _root_.one_mul] at e
    exact mul_eq_left.1 e.symm
  have u₂ : ∀ w, val₂ u z J w (1 : T ⟶ A) = 1 := fun w => by
    have e := (ra 1 1 w).2
    rw [_root_.mul_one, MonObj.one_comp g, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
    exact mul_eq_left.1 e.symm
  have a : ∀ j, val₂ u z J (m ^ j) x * cubN (cubV c z J) j 1 m (x ≫ g) = val₂ u z J m x ^ j := fun j => by
    induction j with
    | zero => simp [cubN, u₁]
    | succ j ih =>
      have e := (ra (m ^ j) m x).1
      rw [hf, C.face₂, _root_.one_mul] at e
      rw [cubN, Finset.prod_range_succ, _root_.one_mul (m ^ j), mul_comm (∏ _ ∈ _, _), ← _root_.mul_assoc, pow_succ m, e,
        pow_succ, ← ih, cubN, mul_right_comm]
  have b : ∀ j, val₂ u z J m (x ^ j) * cubN (cubV c z J) j 1 (x ≫ g) m = val₂ u z J m x ^ j := fun j => by
    induction j with
    | zero => simp [cubN, u₂]
    | succ j ih =>
      have e := (ra (x ^ j) x m).2
      rw [hf, C.face, _root_.one_mul, MonObj.pow_comp, C.s01, C.s12] at e
      rw [cubN, Finset.prod_range_succ, _root_.one_mul ((x ≫ g) ^ j), mul_comm (∏ _ ∈ _, _), ← _root_.mul_assoc, pow_succ x, e,
        pow_succ, ← ih, cubN, mul_right_comm]
  have a' := a k
  have b' := b k
  rw [hm, u₁, _root_.one_mul] at a'
  rw [hx, u₂, _root_.one_mul] at b'
  exact a'.trans b'.symm

omit [IsCommMonObj A] in
theorem twist_val {T : Over S} {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ} {M : LB A.left}
    {α : LB.Gen (LB.LinComb M (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} {s : LB.Sec (LPow A M b T)}
    {s' : LB.Sec (LPow A M a T)} (h : IsTwistPull A M ψ m hm a b α s s') {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J}
    (hJ : Good M z J) : sval (L := M) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' r z J =
      (val α r z J).val * sval (L := M) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (r ≫ ψ.left) z J := by
  let j : Fin 2 → M.ι := fun k => J (r ≫ (![(snd T A).left, m.left] : Fin 2 → _) k)
  have hz : r z ∈ LB.wchart M ![(snd T A).left, m.left] j := hJ.mem _ r
  have e := congrArg (gs r z (LB.wchart M ![(snd T A).left, m.left] j)) (h j)
  have a₁ := gs_res r z (chart_le_zero A M m j) hz (s'.f fun _ => j 0)
  have a₂ := (gs_res r z (chart_le_pull A M ψ m hm j) hz ((ψ.left.app _).hom (s.f fun _ => j 1))).trans
    (gs_pull r ψ.left z (LB.wchart M (fun _ : Fin 1 => (snd T A).left) fun _ => j 1) (chart_le_pull A M ψ m hm j hz) _)
  have a₃ := sval_of (L := M) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (r ≫ ψ.left) z J (fun _ => j 1)
    (fun _ => congrArg J (by rw [Category.assoc, ← Over.comp_left, hm]; rfl))
  exact a₁.symm.trans (e.trans ((gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) (gs_unit r z _ hz _) (a₂.trans a₃.symm))))

theorem sym_val {T : Over S} {k : ℤ} {n : ℕ} {x : T ⟶ A} {M : LB A.left} {U : ThetaGrp A M k T} (h : SymLift A M k n x U) :
    ∃ ν : LB.Gen (negLB A M k T), ν.IsGen ∧ ∀ {T' : Over S} (σ : T' ⟶ T) {z : T'.left} {J}, Good M z J →
      (∏ j ∈ Finset.range n, val (L := M) (φ := ![(snd T A).left, (translPt A U.pt).left]) (ε := ![k, -k]) U.φ
        (lift σ ((σ ≫ U.pt) ^ j)).left z J = 1) ∧
      val (L := M) (φ := ![(snd T A).left, (translPt A U.pt).left]) (ε := ![k, -k]) U.φ (lift σ (σ ≫ U.pt)⁻¹).left z J *
        val (L := M) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) ν (lift σ 1).left z J *
        (val (L := M) (φ := ![(snd T A).left, (translPt A U.pt).left]) (ε := ![k, -k]) U.φ (lift σ 1).left z J *
        (val (L := M) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) ν
          (lift σ (σ ≫ U.pt)⁻¹).left z J)⁻¹) = 1 := by
  obtain ⟨ν, hν, hs⟩ := h.sym
  refine ⟨ν, hν, fun {T'} σ z J hJ => ⟨?_, ?_⟩⟩
  · have e := (val_corr hJ h.pow_eq (lift σ 1).left).trans (val_one _)
    have hz := hJ.mem (powφ A U.pt n) (lift σ (1 : T' ⟶ A)).left
    rw [← Fin.prod_univ_eq_prod_range (fun j => val (L := M) (φ := ![(snd T A).left, (translPt A U.pt).left]) (ε := ![k, -k])
      U.φ (lift σ ((σ ≫ U.pt) ^ j)).left z J)]
    refine Eq.trans (Finset.prod_congr rfl fun j _ => ?_) ((map_prod _ _ _).symm.trans e)
    refine Eq.trans ?_ ((gm_res _ z _ hz _).trans (val_pull hJ U.φ (translT A (U.pt ^ (j : ℕ))).left (lift σ 1).left)).symm
    rw [← Over.comp_left, lift_transl, _root_.mul_one, MonObj.comp_pow]
  · have e := (val_corr hJ hs (lift σ 1).left).trans (val_one _)
    have t₁ : (lift σ (1 : T' ⟶ A)).left ≫ (translT A U.pt⁻¹).left = (lift σ (σ ≫ U.pt)⁻¹).left := by
      rw [← Over.comp_left, lift_transl, _root_.mul_one, GrpObj.comp_inv]
    have t₂ : (lift σ (1 : T' ⟶ A)).left ≫ (negT A T).left = (lift σ 1).left := by
      rw [← Over.comp_left, negT, comp_lift, lift_fst, lift_snd_assoc]
      exact congrArg (fun q => (lift σ q).left) (inv_one : (1 : T' ⟶ A)⁻¹ = 1)
    refine Eq.trans ?_ e
    refine Eq.symm ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_pull hJ _ _ _).trans (by rw [t₁])) rfl)) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_pull hJ _ _ _).trans (by rw [t₂])) ((val_inv _ _).trans (congrArg (·⁻¹) ((val_pull hJ _ _ _).trans (by rw [t₁]))))))))

def VtOver (L : RigLB A) (N : ℕ) {T : Over S} (ok : (T ⟶ A) → Prop) (s : LB.Sec (LPow A L.L 1 T)) (t : T ⟶ A)
    (F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)) : Prop :=
  ∃ (t' : T ⟶ A)
    (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1]))
    (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T A).left, (snd T A ^ N).left] ![(N : ℤ) ^ 2, -1]))
    (s₁ : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)) (U : ThetaGrp A L.L ((N : ℤ) ^ 2) T),
    t' ^ N = t ∧ ok t' ∧ α₀.IsGen ∧ IsNormMul A L.L L.rig N α₀ ∧
    LB.Gen.Corr L.L _ _ _ _ α (LB.pullGen L.L _ _ α₀ (snd T A).left) ∧
    IsTwistPull A L.L (mulT A T N) (snd T A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α s s₁ ∧
    SymLift A L.L ((N : ℤ) ^ 2) (N ^ 2) t' U ∧ IsActOf A L.L ((N : ℤ) ^ 2) U s₁ F

omit [IsCommMonObj A] in
theorem prod_mulN (N : ℕ) {T : Over S} (y : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ A.left) → U) :
    ∏ i, h (y.left ≫ (![𝟙 A.left, (mulA A N).left] : Fin 2 → _) i) ^ (![(N : ℤ) ^ 2, -1] : Fin 2 → ℤ) i =
      h y.left ^ (N ^ 2) * (h (y ^ N).left)⁻¹ := by
  have e : y.left ≫ (mulA A N).left = (y ^ N).left := by
    rw [← Over.comp_left, mulA, comp_pow, Category.comp_id]
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Category.comp_id, e, zpow_neg,
    zpow_one]
  norm_cast

omit [IsCommMonObj A] in
theorem prod_pm (N : ℕ) {T : Over S} (a b : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ A.left) → U) :
    ∏ i, h ((![a.left, b.left] : Fin 2 → _) i) ^ (![(N : ℤ) ^ 2, -(N : ℤ) ^ 2] : Fin 2 → ℤ) i =
      h a.left ^ (N ^ 2) * (h b.left ^ (N ^ 2))⁻¹ := by
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, zpow_neg]
  norm_cast

include c in
set_option maxHeartbeats 1600000 in
theorem vtOver_unique (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hsym : L.IsSymmetric) {N : ℕ} (hN : Odd N) (f g : A ⟶ A)
    [IsMonHom f] [IsMonHom g] (hr : RosatiAdj A L.L f g) {T : Over S} (ok : (T ⟶ A) → Prop)
    (hf : ∀ x, ok x → x ≫ f = 1) (hg : ∀ x, ok x → x ≫ g = x) (hk : ∀ x, ok x → x ^ (N ^ 2) = 1)
    {s : LB.Sec (LPow A L.L 1 T)} {t : T ⟶ A} {F F' : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)} (h : VtOver L N ok s t F)
    (h' : VtOver L N ok s t F') : F = F' := by
  obtain ⟨_, α₀, α, s₁, U, ht, o, g₀, n₀, cα, tw, sl, ac⟩ := h
  obtain ⟨_, α₀', α', s₁', U', ht', o', g₀', n₀', cα', tw', sl', ac'⟩ := h'
  obtain rfl := sl.pt_eq
  obtain rfl := sl'.pt_eq
  obtain ⟨u, hu, nu⟩ := exists_ros hG hA L.isLB f g hr
  obtain ⟨ν', hν', sv'⟩ := sym_val sl
  obtain ⟨ν, hν, sv⟩ := sym_val sl'
  obtain ⟨-, ws, gws, -⟩ := hsym
  obtain ⟨ν₁, hν₁⟩ := gen_of_iso ((isGen_iff ws).1 gws) (𝟙 A.left)
  have ext : ∀ j, F.f j = F'.f j := sec_ext_val (L := L.L) (φ := fun _ : Fin 1 => (snd T A).left) L.isLB fun z J hJ => by
    have C : IsCub (cubV c (T := T ⊗ A) z J) := isCub_cubV c hJ
    let σ := fst T A
    let D : T ⟶ A := U'.pt⁻¹ * U.pt
    have hD : U.pt = U'.pt * D := (mul_inv_cancel_left _ _).symm
    have DN : D ^ N = 1 := by rw [mul_pow, inv_pow, ht, ht', inv_mul_cancel]
    have Dk : D ^ (N ^ 2) = 1 := by rw [pow_two, pow_mul, DN, one_pow]
    have Dg : D ≫ g = D := by rw [MonObj.mul_comp, GrpObj.inv_comp, hg _ o, hg _ o']
    have pk : ∀ {x : T ⟶ A} {n : ℕ}, x ^ n = 1 → (σ ≫ x) ^ n = 1 := fun h => by rw [← MonObj.comp_pow, h, MonObj.comp_one]
    have e₀ : σ ≫ U.pt = (σ ≫ U'.pt) * (σ ≫ D) := by rw [hD, MonObj.comp_mul]
    have bb : ∀ y : T ⊗ A ⟶ A, val α₀' y.left z J = val α₀ y.left z J := fun y =>
      gen_unique L.isLB A.hom (eSec A) (Over.w η[A]) (hG _ _ hA).2 g₀' g₀ (fun w I hI => by
        have a := val_corr hI n₀' (𝟙 _)
        have b := val_corr hI n₀ (𝟙 _)
        rw [val_pull hI, Category.id_comp] at a b
        exact a.trans b.symm) _ _ z J hJ
    have vp : ∀ (m : T ⊗ A ⟶ A) (y : T ⊗ A ⟶ A), val (LB.pullGen L.L _ _ α₀ m.left) (lift σ y).left z J =
        val α₀ (lift σ y ≫ m).left z J := fun m y => val_pull hJ _ _ _
    have tp : ∀ (x : T ⟶ A) (y : T ⊗ A ⟶ A), lift σ y ≫ translPt A x = y * (σ ≫ x) := fun x y => by
      rw [translPt_eq, MonObj.comp_mul, lift_fst_assoc, lift_snd, mul_comm]
    have hc := fun y => ratio_const hG hA L.isLB (fun V _ k => by
        refine (prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (prod_pm N _ _ k) (prod_mulN N (translPt A U'.pt) k)).trans
          (Eq.trans ?_ (prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (prod_pm N _ _ k) (prod_mulN N (translPt A U.pt) k)).symm)
        have : translPt A U'.pt ^ N = translPt A U.pt ^ N := by
          rw [translPt_eq, translPt_eq, mul_pow, mul_pow, ← MonObj.comp_pow, ← MonObj.comp_pow, ht, ht']
        rw [this]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel) (mulGen_isGen _ _ _ _ _ _ _ U.isGen (pullGen_isGen _ _ _ _ g₀ (translPt A U.pt).left))
      (mulGen_isGen _ _ _ _ _ _ _ U'.isGen (pullGen_isGen _ _ _ _ g₀ (translPt A U'.pt).left)) σ y hJ
    have evU : ∀ (W : ThetaGrp A L.L ((N : ℤ) ^ 2) T) (y : T ⊗ A ⟶ A), val (LB.mulGen L.L ![(snd T A).left, (translPt A W.pt).left]
        ![(N : ℤ) ^ 2, -(N : ℤ) ^ 2] _ _ W.φ (LB.pullGen L.L _ _ α₀ (translPt A W.pt).left)) (lift σ y).left z J =
        val (L := L.L) (φ := ![(snd T A).left, (translPt A W.pt).left]) (ε := ![(N : ℤ) ^ 2, -(N : ℤ) ^ 2]) W.φ
          (lift σ y).left z J * val α₀ (y * (σ ≫ W.pt)).left z J := fun W y =>
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((vp _ y).trans (by rw [tp])))
    have hc := fun y => (congrArg₂ (· * ·) (evU U y) (evU U' 1)).symm.trans ((hc y).trans
      (congrArg₂ (· * ·) (evU U' y) (evU U 1)))
    have vφ := fun y => val_theta c hG hA (hk _ o') (φ := ![(snd T A).left, (translPt A U'.pt).left]) U'.φ U'.isGen
      (fun V _ k => prod_pm N _ _ k) σ y hJ
    have vδ := fun y => val_theta c hG hA Dk (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ α₀ (snd T A).left)
      (LB.invGen L.L _ _ (LB.pullGen L.L _ _ α₀ (translPt A D).left)))
      (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ g₀ _) (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ g₀ _)))
      (fun V _ k => by
        refine (prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (prod_mulN N (snd T A) k)
          (prod_neg _ _ (prod_mulN N (translPt A D) k))).trans ?_
        rw [translPt_eq, mul_pow, ← MonObj.comp_pow, DN, MonObj.comp_one, _root_.one_mul]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel) σ y hJ
    have evD : ∀ y : T ⊗ A ⟶ A, val (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ α₀ (snd T A).left)
        (LB.invGen L.L _ _ (LB.pullGen L.L _ _ α₀ (translPt A D).left))) (lift σ y).left z J =
        val α₀ y.left z J * (val α₀ (y * (σ ≫ D)).left z J)⁻¹ := fun y =>
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((vp _ y).trans (by rw [lift_snd]))
        ((val_inv _ _).trans (congrArg (·⁻¹) ((vp _ y).trans (by rw [tp])))))
    have vδ := fun y => (evD y).symm.trans (vδ y)
    have iso := ros_pow' c hG hA f g u hu nu hJ (x := σ ≫ D) (m := σ ≫ U'.pt) (pk Dk) (pk (hk _ o'))
      (by rw [Category.assoc, hf _ o', MonObj.comp_one])
    rw [Category.assoc, Dg] at iso
    have hn := fun y => ratio_const hG hA L.isLB (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left])
      (fun _ _ _ => rfl) hν' hν σ y hJ
    have hκ := fun y => ratio_const hG hA L.isLB (fun V _ k => by
        refine (prod_two (𝟙 _) ((snd T A ^ N)⁻¹) (snd T A ^ N) 1 (-1) k |> fun p => Eq.trans ?_ (p.trans ?_))
        · refine Finset.prod_congr rfl fun i _ => congrArg (fun q => k q ^ _) ?_
          fin_cases i
          · exact (congrArg (_ ≫ ·) (Category.id_comp _)).trans (Category.id_comp _).symm
          · exact (Category.comp_id _).trans (Category.id_comp _).symm
        · refine Eq.trans ?_ (prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := Fin 2) (U := V) _
            (prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (prod_mulN N (snd T A) k) (prod_neg _ _ (prod_mulN N (snd T A)⁻¹ k)))
            (prod_neg _ _ (prod_pm N (snd T A) (snd T A)⁻¹ k))).symm
          rw [Category.id_comp, Category.id_comp, inv_pow]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv, ofMul_zpow, one_zsmul, neg_zsmul]
          abel)
      (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ g₀ (snd T A).left)
        (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ g₀ (snd T A)⁻¹.left)))
        (invGen_isGen L.L ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] _ ν hν))
      (pullGen_isGen _ _ _ _ hν₁ (snd T A ^ N).left) σ y hJ
    have evK : ∀ y : T ⊗ A ⟶ A, val (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ α₀ (snd T A).left)
        (LB.invGen L.L _ _ (LB.pullGen L.L _ _ α₀ (snd T A)⁻¹.left)))
        (LB.invGen L.L ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] ![(N : ℤ) ^ 2, -(N : ℤ) ^ 2] ν))
        (lift σ y).left z J = val α₀ y.left z J * (val α₀ y⁻¹.left z J)⁻¹ *
          (val (L := L.L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left])
            (ε := ![(N : ℤ) ^ 2, -(N : ℤ) ^ 2]) ν (lift σ y).left z J)⁻¹ := fun y =>
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((vp _ y).trans (by rw [lift_snd])) ((val_inv _ _).trans (congrArg (·⁻¹) ((vp _ y).trans
          (by rw [GrpObj.comp_inv, lift_snd])))))) (val_inv _ _))
    have evN : ∀ y : T ⊗ A ⟶ A, val (LB.pullGen L.L _ _ ν₁ (snd T A ^ N).left) (lift σ y).left z J =
        val ν₁ (y ^ N).left z J := fun y => by rw [val_pull hJ, ← Over.comp_left, MonObj.comp_pow, lift_snd]
    have hκ := fun y => (congrArg₂ (· * ·) (evK y) rfl).symm.trans ((hκ y).trans (congrArg₂ (· * ·) (evN y) rfl))
    obtain ⟨p', q'⟩ := sv' σ hJ
    obtain ⟨p, q⟩ := sv σ hJ
    rw [e₀] at p' q' hc
    have c1 := lift_const (hN.pow (n := 2)) (pk (hk _ o')) (pk Dk)
      (fun y => val (L := L.L) (φ := ![(snd T A).left, (translPt A U.pt).left]) U.φ (lift σ y).left z J)
      (fun y => val (L := L.L) (φ := ![(snd T A).left, (translPt A U'.pt).left]) U'.φ (lift σ y).left z J)
      (fun y => val α₀ y.left z J)
      (fun y => val (L := L.L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) ν' (lift σ y).left z J)
      (fun y => val (L := L.L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) ν (lift σ y).left z J)
      (fun y => val α₀ y.left z J * (val α₀ y⁻¹.left z J)⁻¹ *
        (val (L := L.L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) ν (lift σ y).left z J)⁻¹) _ _
      (fun y => by
        have a₁ := vδ y
        have a₂ := vδ (y * (σ ≫ U'.pt))
        have a₃ := cubN_right C (pk (hk _ o')) y (σ ≫ D)
        have a₄ := cubN_right C (pk Dk) y (σ ≫ U'.pt)
        rw [C.s01, C.s12, C.s01] at a₄
        rw [mul_right_comm y] at a₂
        rw [vφ (y * (σ ≫ D)), vφ y]
        apply Additive.ofMul.injective
        have E := fun {p q : ((T ⊗ A).left.presheaf.stalk z)ˣ} (e : p = q) => congrArg Additive.ofMul e
        have b₁ := E a₁; have b₂ := E a₂; have b₃ := E a₃; have b₄ := E a₄; have b₅ := E iso
        simp only [ofMul_mul, ofMul_inv] at b₁ b₂ b₃ b₄ b₅ ⊢
        linear_combination (norm := abel) b₁ - b₂ + b₃ - b₄ + b₅)
      (fun y => (eq_mul_inv_of_mul_eq (hc y)).trans ((_root_.mul_assoc _ _ _).trans (mul_comm _ _))) p' p q' q
      (fun y => (eq_mul_inv_of_mul_eq (hn y)).trans ((_root_.mul_assoc _ _ _).trans (mul_comm _ _)))
      (fun y => by
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel)
      (by
        have a₁ := hκ ((σ ≫ U'.pt) * (σ ≫ D))⁻¹
        have a₂ := hκ (σ ≫ U'.pt)⁻¹
        rw [inv_pow, mul_pow, pk DN, _root_.mul_one] at a₁
        rw [inv_pow] at a₂
        exact mul_right_cancel (a₁.trans a₂.symm))
    have fin := hc (snd T A)
    rw [mul_inv_eq_one.1 c1] at fin
    have fin' := mul_right_cancel fin
    have i₁ : (lift σ (snd T A)).left = 𝟙 _ := congrArg (fun q => q.left) (lift_fst_snd : lift (fst T A) (snd T A) = 𝟙 _)
    have va : ∀ {β₀ β} (_ : LB.Gen.Corr L.L _ _ _ _ β (LB.pullGen L.L _ _ β₀ (snd T A).left)) (y : T ⊗ A ⟶ A),
        val (L := L.L) (φ := ![(snd T A).left, (snd T A ^ N).left]) (ε := ![(N : ℤ) ^ 2, -1]) β (lift σ y).left z J =
          val (L := L.L) (φ := ![𝟙 A.left, (mulA A N).left]) (ε := ![(N : ℤ) ^ 2, -1]) β₀ y.left z J := fun h y =>
      (val_corr hJ h _).trans ((val_pull hJ _ _ _).trans (by rw [← Over.comp_left, lift_snd]))
    have mt : ∀ y : T ⊗ A ⟶ A, (lift σ y).left ≫ (mulT A T N).left = (lift σ (y ^ N)).left := fun y => by
      rw [← Over.comp_left, mulT, comp_lift, lift_fst, MonObj.comp_pow, lift_snd]
    have w₁ := twist_val ac (lift σ (snd T A)).left z hJ
    have w₂ := twist_val ac' (lift σ (snd T A)).left z hJ
    rw [← Over.comp_left, lift_transl, twist_val tw _ z hJ, mt, mul_comm (σ ≫ _), mul_pow, ← MonObj.comp_pow, ht] at w₁
    rw [← Over.comp_left, lift_transl, twist_val tw' _ z hJ, mt, mul_comm (σ ≫ _), mul_pow, ← MonObj.comp_pow, ht'] at w₂
    rw [← i₁]
    refine w₁.trans (Eq.trans ?_ w₂.symm)
    rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul]
    refine congrArg₂ (· * ·) (congrArg Units.val ?_) rfl
    refine (congrArg₂ (· * ·) rfl ((va cα _).trans (by rw [e₀]))).trans (fin'.trans (congrArg₂ (· * ·) rfl ?_))
    exact ((va cα' _).trans (bb _)).symm
  cases F; cases F'; congr; exact funext ext

theorem gen_of_lbIso {X Y : Scheme.{0}} {M : LB X} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (h : LBIso (LB.LinComb M φ ε) (LB.LinComb M φ' ε')) :
    ∃ t : LB.Gen (LB.LinComb M (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k)), t.IsGen := by
  obtain ⟨w, hw⟩ := h
  have le : ∀ j : K' ⊕ K → M.ι, LB.wchart M (Sum.elim φ' φ) j ≤
      LB.wchart M φ' (j ∘ Sum.inl) ⊓ LB.wchart M φ (j ∘ Sum.inr) := fun j y hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k), Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)⟩
  refine ⟨⟨fun j => res (le j) (w.s (j ∘ Sum.inl, j ∘ Sum.inr))⟩, isGen_of_gm _ fun y j j' hj hj' => ?_⟩
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ (LB.wchart M φ' (j ∘ Sum.inl) ⊓ LB.wchart M φ (j ∘ Sum.inr)) ⊓
      (LB.wchart M φ' (j' ∘ Sum.inl) ⊓ LB.wchart M φ (j' ∘ Sum.inr)) := ⟨le j hj, le j' hj'⟩
  have e₀ := congrArg (gm (𝟙 Y) y _) (hw (j ∘ Sum.inl, j ∘ Sum.inr) (j' ∘ Sum.inl, j' ∘ Sum.inr))
  have e₁ := (gm_div (LB.LinComb M φ ε) (LB.LinComb M φ' ε') (𝟙 Y) y (j ∘ Sum.inl, j ∘ Sum.inr) (j' ∘ Sum.inl, j' ∘ Sum.inr)
    hm).trans (congrArg₂ (fun a b => a * b⁻¹) (gm_linComb M φ' ε' (𝟙 Y) y _ _ hm.1.1 hm.2.1)
      (gm_linComb M φ ε (𝟙 Y) y _ _ hm.1.2 hm.2.2))
  refine (gm_res (𝟙 Y) y (le j) hj _).trans (((gm_res (𝟙 Y) y inf_le_left hm _).symm.trans (e₀.trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) e₁ (gm_res (𝟙 Y) y inf_le_right hm _))))).trans
    (congrArg₂ (· * ·) ?_ (gm_res (𝟙 Y) y (le j') hj' _).symm))
  rw [trF, Fintype.prod_sum_type]
  exact congrArg₂ (· * ·) rfl (prod_neg _ ε rfl).symm

theorem prod_cube₂ {T : Over S} (x y : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ A.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h (psum A ![x, y] I.down).left ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : T ⟶ A).left := by
  have hpadd : ∀ a b : T ⟶ A, padd A a b = a * b := fun a b => rfl
  have hpzero : pzero A T = (1 : T ⟶ A) := rfl
  rw [← Equiv.prod_comp Equiv.ulift.symm]
  have hU : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [hU, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  simp (config := {decide := true}) [psum, hpadd, hpzero, List.finRange, Equiv.ulift]
  simp only [_root_.mul_comm, _root_.mul_assoc, _root_.mul_left_comm]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem SAB.rosatiAdj (t : SAB H S) (a : 𝓞 E) : RosatiAdj t.G t.PP.L (t.act.act a) (t.act.act (H.bar a)) := fun s => by
  obtain ⟨u, hu⟩ := gen_of_lbIso (LBIso.symm (t.adj a))
  obtain ⟨v, hv, -⟩ := exists_gen t.PP.isLB (φ' := rosatiφ t.G (t.act.act a) (t.act.act (H.bar a))) (ε' := rosatiε)
    (fun U _ k => by
      have p := prod_ros (t.act.act a) (t.act.act (H.bar a)) (fst t.G t.G) (snd t.G t.G) k
      rw [lift_fst_snd] at p
      simp only [Over.id_left, Category.id_comp] at p
      refine (prod_sum₂ (K := ULift.{0} (Finset (Fin 2))) (K' := ULift.{0} (Finset (Fin 2))) (U := U) _ (prod_cube₂ _ _ k)
        (prod_neg _ _ (prod_cube₂ _ _ k))).trans (Eq.trans ?_ p.symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) u hu
  exact ⟨⊤, trivial, _, pullGen_isGen _ _ _ v hv _⟩

theorem vtUniq_obj (hG : GlobalFnsSt) {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {s₀ : S ⟶ Sp B}
    (o : Obj D l b s₀) {T : Over S} {s : LB.Sec (LPow o.t.G o.t.PP.L 1 T)} {t : T ⟶ o.t.G}
    {F F' : LB.Sec (LPow o.t.G o.t.PP.L ((l.M : ℤ) ^ 2) T)}
    (h : VtOver o.t.PP l.M (fun x => ∀ a ∈ l.Mb ^ 2, x ≫ o.t.act.act a = 1) s t F)
    (h' : VtOver o.t.PP l.M (fun x => ∀ a ∈ l.Mb ^ 2, x ≫ o.t.act.act a = 1) s t F') : F = F' := by
  have cop : l.Mb ^ 2 ⊔ (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2 = ⊤ := Ideal.sup_pow_eq_top' (Ideal.pow_sup_eq_top l.coprime)
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 (cop.ge (Submodule.mem_top : (1 : 𝓞 E) ∈ ⊤))
  rw [← Ideal.map_pow, Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective] at hq
  obtain ⟨a, ha, rfl⟩ := hq
  have := o.t.act.hom a
  have := o.t.act.hom (H.bar a)
  have nat : ∀ n : ℕ, o.t.act.act n = 𝟙 o.t.G ^ n := fun n => by
    induction n with
    | zero =>
      have h := o.t.act.add 0 0
      rw [add_zero] at h
      rw [Nat.cast_zero, pow_zero]; exact mul_eq_left.1 h.symm
    | succ n ih => rw [Nat.cast_succ, o.t.act.add, ih, o.t.act.one, pow_succ]
  refine vtOver_unique o.t.cub hG ⟨inferInstance, o.t.semi.smooth, o.proper, o.t.semi.geomConnected⟩ o.t.sym l.odd _ _
    (o.t.rosatiAdj a) _ (fun x hx => hx a ha) (fun x hx => ?_) (fun x hx => ?_) h h'
  · have e : x ≫ o.t.act.act (p + H.bar a) = x := by rw [show p + H.bar a = 1 from hpq, o.t.act.one, Category.comp_id]
    rwa [o.t.act.add, MonObj.comp_mul, hx p hp, _root_.one_mul] at e
  · have m : ((l.M ^ 2 : ℕ) : 𝓞 E) ∈ l.Mb ^ 2 := by
      rw [Nat.cast_pow]
      exact Ideal.pow_mem_pow (Ideal.mul_le_left (l.prod.ge (Ideal.subset_span rfl))) 2
    have e := hx _ m
    rwa [nat, MonObj.comp_pow, Category.comp_id] at e

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
