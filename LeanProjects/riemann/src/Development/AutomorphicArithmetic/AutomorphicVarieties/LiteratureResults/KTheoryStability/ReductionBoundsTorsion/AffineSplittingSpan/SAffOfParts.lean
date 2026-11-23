import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.InclInj

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.SplitAffineSpectral

open GluingInclusion

private theorem monoidHom_partialProd_comm {P : Type} [Group P] (σ : P →* P) {k : ℕ} (g : Fin k → P) (i : Fin (k + 1)) :
    σ (Fin.partialProd g i) = Fin.partialProd (fun l => σ (g l)) i := by
  induction i using Fin.induction with
  | zero => simp [Fin.partialProd_zero]
  | succ i ih => rw [Fin.partialProd_succ, Fin.partialProd_succ, map_mul, ih]

private theorem H_affine_combination_eq_of_quadratic_relation (hCh : SChain) (hSep : SSep) (hCore : Core) (hEv : EvCob)
    {P Q : Type} [Group P] [Group Q] (pr : P →* Q) (s : Q →* P) (hs : ∀ g, pr (s g) = g)
    (u : Q) (hu : ∀ g, g * u = u * g) {m : ℕ} (hC : ColPoly pr s u m) {j : ℕ} (hj : j + 1 ≤ m)
    (w : Chn P (j + 1)) (hw : IsCyc w) : IsBd (w - cmap (s.comp pr) (j + 1) w) := by
  set σ := s.comp pr with hσdef
  have hσσ : ∀ x, σ (σ x) = σ x := by intro x; simp [σ, hs]
  have hcyc : IsCyc (w - cmap σ (j + 1) w) := by
    unfold IsCyc at hw ⊢
    rw [map_sub, hCh.2.1 P P σ j w, hw, map_zero, sub_zero]
  by_contra hnb
  obtain ⟨c, hcI, hcd, hce⟩ := hSep P j _ hcyc hnb
  set c' : (Fin (j + 2) → P) → ℝ := fun y => c y - c (fun i => σ (y i)) with hc'
  have hI : InvS Set.univ c' := by
    intro g _ y
    have h1 := hcI g y
    have h2 := hcI (σ g) (fun i => σ (y i))
    simp only [MonoidHom.id_apply, smul_eq_mul] at h1 h2
    simp only [c', map_mul, h1, h2]
  have hd : dc c' = 0 := by
    funext y
    have e1 := congrFun hcd y
    have e2 := congrFun hcd (fun i => σ (y i))
    simp only [dC, Pi.zero_apply] at e1 e2
    simp only [dc, c', Pi.zero_apply, mul_sub, Finset.sum_sub_distrib, e1, e2, sub_zero]
  have hvan : ∀ y : Fin (j + 2) → Q, c' (fun i => s (y i)) = 0 := by
    intro y; simp [c', σ, hs]
  obtain ⟨e, heI, hce'⟩ := hCore P Q pr s hs u hu m hC j hj c' hI hd hvan
  have heI' : Inv (MonoidHom.id P) e := by
    intro g y
    simpa using heI g (Set.mem_univ g) y
  have hev0 := hEv P j e heI' _ hcyc
  apply hce
  have hdd : dC e = c' := hce'.symm
  rw [hdd] at hev0
  rw [← hev0]
  unfold ev
  simp only [c', mul_sub, Finsupp.sum_sub]
  rw [eq_comm, sub_eq_self]
  have hcm : cmap σ (j + 1) w = Finsupp.mapDomain (fun g i => σ (g i)) w := rfl
  rw [hcm, Finsupp.sum_sub_index (by intros; ring),
    Finsupp.sum_mapDomain_index (by intros; simp) (by intros; ring)]
  simp only [MonoidHom.id_apply, smul_eq_mul, mul_one, monoidHom_partialProd_comm, hσσ, sub_self]

private theorem aeval_mapOp_dc_comm {A : Type} (φ : A → A) (k : ℕ) (f : Polynomial ℝ)
    (e : (Fin (k + 1) → A) → ℝ) :
    Polynomial.aeval (mapOp φ (k + 2)) f (dc e) = dc (Polynomial.aeval (mapOp φ (k + 1)) f e) := by
  have hadd : ∀ a b : (Fin (k + 1) → A) → ℝ, dc (a + b) = dc a + dc b := by
    intro a b; funext y; simp [dc, mul_add, Finset.sum_add_distrib]
  have hsmul : ∀ (t : ℝ) (a : (Fin (k + 1) → A) → ℝ), dc (t • a) = t • dc a := by
    intro t a; funext y; simp [dc, Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
  have hpow : ∀ (N : ℕ) (a : (Fin (k + 1) → A) → ℝ),
      (mapOp φ (k + 2) ^ N) (dc a) = dc ((mapOp φ (k + 1) ^ N) a) := by
    intro N
    induction N with
    | zero => intro a; rfl
    | succ N ih =>
      intro a
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
      have : mapOp φ (k + 2) (dc a) = dc (mapOp φ (k + 1) a) := rfl
      rw [this, ih]
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq, hadd]
  | monomial N a =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, hpow, hsmul]

private theorem invS_aeval_mapOp_of_invS_of_mul_hom {A : Type} [Group A] (φ : A → A) (hφ : ∀ x y, φ (x * y) = φ x * φ y)
    (k : ℕ) (f : Polynomial ℝ) (e : (Fin k → A) → ℝ) (he : InvS Set.univ e) :
    InvS Set.univ (Polynomial.aeval (mapOp φ k) f e) := by
  have hpow : ∀ (N : ℕ) (a : (Fin k → A) → ℝ), InvS Set.univ a →
      InvS Set.univ ((mapOp φ k ^ N) a) := by
    intro N
    induction N with
    | zero => intro a ha; simpa using ha
    | succ N ih =>
      intro a ha
      rw [pow_succ, Module.End.mul_apply]
      apply ih
      intro g _ y
      show a (fun i => φ (g * y i)) = a (fun i => φ (y i))
      simp only [hφ]
      exact ha (φ g) (Set.mem_univ _) _
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    intro g hg y
    simp only [map_add, LinearMap.add_apply, Pi.add_apply, hp g hg y, hq g hg y]
  | monomial N a =>
    intro g hg y
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [hpow N e he g hg y]

private theorem aPoly_mulV_of_unit_place_monomials_ne_one (hSpan : Span) (hEig : Eigen) {L : Type} [Field L] [NumberField L]
    (hL : IsTotallyComplex L) (m : ℕ) (v : (𝓞 L)ˣ)
    (hv : ∀ a : InfinitePlace L → ℕ, 0 < ∑ w, a w → ∑ w, a w ≤ m →
      ∏ w, w (algebraMap (𝓞 L) L ↑v) ^ a w ≠ 1) (n r : ℕ) :
    APoly (Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L))) (mulV n r ↑v) m := by
  intro q hq
  obtain ⟨f, hf1, hf⟩ := hEig L hL m v hv n r q hq
  refine ⟨f, hf1, ?_⟩
  intro c hcI hcd
  haveI : Module.Free ℤ (Additive (Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L)))) :=
    (inferInstance : Module.Free ℤ (Matrix (Fin n) (Fin r) (𝓞 L)))
  haveI : Module.Finite ℤ (Additive (Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L)))) :=
    (inferInstance : Module.Finite ℤ (Matrix (Fin n) (Fin r) (𝓞 L)))
  obtain ⟨k, a, α, e, heI, rfl⟩ := hSpan _ q c hcI hcd
  refine ⟨Polynomial.aeval (mapOp (mulV n r ↑v) (q + 1)) f e, ?_, ?_⟩
  · apply invS_aeval_mapOp_of_invS_of_mul_hom _ _ _ _ _ heI
    intro x y
    unfold mulV
    simp [smul_add]
  · rw [map_add, map_sum]
    simp only [map_smul, hf, smul_zero, Finset.sum_const_zero, zero_add]
    exact aeval_mapOp_dc_comm _ q f e

theorem sAff_of_parts (hCh : SChain) (hSep : SSep) (hCore : Core) (hTr : Transfer) (hSpan : Span)
    (hUnit : Unit) (hEig : Eigen) (hEv : EvCob) : SAff := by
  intro L _ _ hL k hk n r H _ f f₀ hblock z hz
  obtain ⟨v, hv⟩ := hUnit L hL (k + 1) hk
  let ψ : GL (Fin n) (𝓞 L) →* MulAut (Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L))) :=
    { toFun := fun g =>
        { toFun := fun B => Multiplicative.ofAdd ((g : Matrix (Fin n) (Fin n) (𝓞 L)) * Multiplicative.toAdd B)
          invFun := fun B => Multiplicative.ofAdd (((g⁻¹ : GL (Fin n) (𝓞 L)) : Matrix (Fin n) (Fin n) (𝓞 L)) *
            Multiplicative.toAdd B)
          left_inv := fun B => by simp [← Matrix.mul_assoc]
          right_inv := fun B => by simp [← Matrix.mul_assoc]
          map_mul' := fun B C => by simp [Matrix.mul_add] }
      map_one' := by ext B; simp
      map_mul' := fun g h => by ext B; simp [Matrix.mul_assoc] }
  let Φ₀ : Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L)) ⋊[ψ] GL (Fin n) (𝓞 L) →*
      Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L) :=
    { toFun := fun p => Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (p.right : Matrix (Fin n) (Fin n) (𝓞 L)) (Multiplicative.toAdd p.left) 0 1)
      map_one' := by simp
      map_mul' := fun p q => by
        simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, Matrix.reindex_apply,
          Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
        congr 1
        simp [ψ, add_comm] }
  let Φ : Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L)) ⋊[ψ] GL (Fin n) (𝓞 L) →* GL (Fin (n + r)) (𝓞 L) :=
    Φ₀.toHomUnits
  have hΦv : ∀ p, ((Φ p : GL (Fin (n + r)) (𝓞 L)) : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (p.right : Matrix (Fin n) (Fin n) (𝓞 L)) (Multiplicative.toAdd p.left) 0 1) :=
    fun p => rfl
  have hinj : Function.Injective Φ := by
    intro p q hpq
    have h1 := congrArg Units.val hpq
    rw [hΦv, hΦv] at h1
    have h2 := (Matrix.reindex finSumFinEquiv finSumFinEquiv).injective h1
    rw [Matrix.fromBlocks_inj] at h2
    exact SemidirectProduct.ext h2.2.1 (Units.ext h2.1)
  choose B hB using hblock
  have hΦf : ∀ x, Φ ⟨Multiplicative.ofAdd (B x), f₀ x⟩ = f x := by
    intro x
    apply Units.ext
    rw [hΦv]
    exact (hB x).symm
  let f' : H →* Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L)) ⋊[ψ] GL (Fin n) (𝓞 L) :=
    { toFun := fun x => ⟨Multiplicative.ofAdd (B x), f₀ x⟩
      map_one' := hinj (by rw [hΦf, map_one, map_one])
      map_mul' := fun x y => hinj (by rw [map_mul Φ, hΦf, hΦf, hΦf, map_mul f]) }
  let u : GL (Fin n) (𝓞 L) := Units.map (Matrix.scalar (Fin n) : 𝓞 L →+* Matrix (Fin n) (Fin n) (𝓞 L)).toMonoidHom v⁻¹
  have hu : ∀ g, g * u = u * g := by
    intro g
    apply Units.ext
    simp only [Units.val_mul, u, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    exact ((Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq).symm
  let χ := (ψ u⁻¹).toMonoidHom
  have hχ : ∀ a, SemidirectProduct.inl (φ := ψ) (χ a) =
      (SemidirectProduct.inr (φ := ψ) u)⁻¹ * SemidirectProduct.inl (φ := ψ) a *
        SemidirectProduct.inr (φ := ψ) u := by
    intro a
    have := SemidirectProduct.inl_aut (φ := ψ) u⁻¹ a
    rw [inv_inv, (SemidirectProduct.inr (φ := ψ)).map_inv u] at this
    exact this
  have hχeq : (χ : Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L)) → _) = mulV n r ↑v := by
    funext a
    simp [χ, ψ, u, mulV, Matrix.smul_eq_diagonal_mul]
  have hA : APoly (Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L))) χ (k + 1) := by
    rw [hχeq]
    exact aPoly_mulV_of_unit_place_monomials_ne_one hSpan hEig hL (k + 1) v hv n r
  have hC : ColPoly (SemidirectProduct.rightHom (φ := ψ)) SemidirectProduct.inr u (k + 1) := by
    refine hTr _ _ _ _ _ (fun g => SemidirectProduct.rightHom_inr g) u hu SemidirectProduct.inl
      SemidirectProduct.inl_injective ?_ χ hχ (k + 1) hA
    intro x
    rw [SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
  have hs : ∀ g, SemidirectProduct.rightHom (φ := ψ) (SemidirectProduct.inr g) = g :=
    SemidirectProduct.rightHom_inr
  have hΦs : ∀ g, stab (𝓞 L) n (n + r) (Nat.le_add_right n r) g = Φ (SemidirectProduct.inr g) := by
    intro g
    apply Units.ext
    rw [hΦv]
    ext i j
    unfold stab padHom
    simp only [Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk]
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;>
      refine Fin.addCases (fun c => ?_) (fun d => ?_) j <;>
      simp [padMat, Matrix.reindex_apply, Matrix.one_apply, Fin.ext_iff]
    all_goals (intro h; first | (have := a.isLt; omega) | (have := c.isLt; omega))
  let w := cmap f' (k + 1) z
  have hw : IsCyc w := by
    unfold IsCyc at hz ⊢
    rw [hCh.2.1 H _ f' k z, hz, map_zero]
  have hb := H_affine_combination_eq_of_quadratic_relation hCh hSep hCore hEv _ _ hs u hu hC (j := k) le_rfl w hw
  have hf : f = Φ.comp f' := MonoidHom.ext fun x => (hΦf x).symm
  have e1 : cmap f (k + 1) z = cmap Φ (k + 1) w := by
    rw [hf, hCh.2.2.1]
  have e2 : cmap ((stab (𝓞 L) n (n + r) (Nat.le_add_right n r)).comp f₀) (k + 1) z =
      cmap Φ (k + 1) (cmap ((SemidirectProduct.inr (φ := ψ)).comp SemidirectProduct.rightHom) (k + 1) w) := by
    have hst : (stab (𝓞 L) n (n + r) (Nat.le_add_right n r)).comp f₀ =
        Φ.comp (((SemidirectProduct.inr (φ := ψ)).comp SemidirectProduct.rightHom).comp f') :=
      MonoidHom.ext fun x => hΦs (f₀ x)
    rw [hst, hCh.2.2.1, hCh.2.2.1]
  rw [e1, e2, ← map_sub]
  unfold IsBd at hb ⊢
  obtain ⟨y, hy⟩ := hb
  exact ⟨cmap Φ (k + 1 + 1) y, by rw [hCh.2.1, hy]⟩

end PositivityTheory.KB.SplitAffineSpectral

end
