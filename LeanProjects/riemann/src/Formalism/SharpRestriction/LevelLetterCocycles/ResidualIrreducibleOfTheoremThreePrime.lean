import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleThreePrime
import Formalism.CyclotomicNorms.IrreducibilityOfGoodTuple
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleOfTheorem

noncomputable section

namespace Formalism.MainNotions.AdmissibleThreePrime

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem parts_of (D : D7) (i : D.nd.Loc) (x : D.nd.X i) (Sig : List (Formalism.BasicNotions.Part D.naut.CG))
    (hx : HasParamX D.nd D.naut i x Sig) :
    (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d) ∧ rankIso D.nd D.naut Sig = D.R.r := by
  obtain ⟨P, -, hBC⟩ := hx
  refine ⟨fun p hp => ?_, ?_⟩
  · have hm : (⟨p.a, D.naut.tw p.π D.naut.etaTinv, p.d⟩ : Formalism.BasicNotions.Part D.naut.CG) ∈
        twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv :=
      List.mem_map.2 ⟨p, List.mem_append_left _ hp, rfl⟩
    exact ⟨(hBC.1 _ hm).1, (hBC.1 _ hm).2.1⟩
  · have h := hBC.2.2.1
    have e : rankIso D.nd D.naut (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) =
        rankIso D.nd D.naut Sig + D.R.t := by
      simp [rankIso, twistIso, muPart, List.map_map, Function.comp_def]
    rw [e] at h
    have : D.R.nV = D.R.r + D.R.t := rfl
    omega

theorem cusp_of (D : D7) (hT : SumRepresentations.tieLab D) (i : D.nd.Loc) (x : D.nd.X i)
    (Sig : List (Formalism.BasicNotions.Part D.naut.CG)) (hx : HasParamX D.nd D.naut i x Sig)
    (hg : goodSig D.nd D.naut Sig) : IsCuspIso D.nd D.naut Sig := by
  obtain ⟨hpos, hrank⟩ := parts_of D i x Sig hx
  let k : Fin 2 := 0
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨h1, h2, -, -, h5, -⟩ := (hg k).1
  have : Nonempty (D.nd.PlG k) := by
    rw [← Fintype.card_pos_iff, D.nd.card_PlG k]
    show 0 < 2 * D.R.n
    have := D.R.ord_pos
    show 0 < 2 * D.R.ord
    omega
  have hr : 1 ≤ D.R.r := by
    have := D.R.two_le_m
    show 1 ≤ D.R.k + D.R.m - 1
    omega
  have hf : ∀ v, D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v)) =
      ∏ j : Fin Sig.length,
        D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v)) ^ (Sig.get j).d := by
    intro v
    rw [SumRepresentations.inertiaCharpoly_eq_of_iso D.nd D.naut hT k v Sig,
      SumRepresentations.list_prod_fin Sig (fun p => D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG p.π (D.naut.plGw k v)) ^ p.d)]
  have hrk : ∑ j : Fin Sig.length, (Sig.get j).a * (Sig.get j).d = D.R.r := by
    rw [← hrank, rankIso, SumRepresentations.list_sum_fin Sig (fun p => p.a * p.d)]
  have hd : ∀ j : Fin Sig.length, 1 ≤ (Sig.get j).a ∧ 1 ≤ (Sig.get j).d :=
    fun j => hpos _ (List.get_mem Sig j)
  have hdeg : ∀ v (j : Fin Sig.length),
      (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v))).natDegree =
        (Sig.get j).a := by
    intro v
    have hne : ∀ j ∈ (Finset.univ : Finset (Fin Sig.length)),
        D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v)) ^ (Sig.get j).d ≠ 0 := by
      rw [← Finset.prod_ne_zero_iff, ← hf v]
      exact (h1 v).1.ne_zero
    have hsum : ∑ j : Fin Sig.length,
        (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v))).natDegree *
          (Sig.get j).d =
        ∑ j : Fin Sig.length, (Sig.get j).a * (Sig.get j).d := by
      have h1' : (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).natDegree = D.R.r :=
        (h1 v).2.1
      rw [hrk, ← h1', hf v, natDegree_prod _ _ hne]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [natDegree_pow, mul_comm]
    have hle : ∀ j ∈ (Finset.univ : Finset (Fin Sig.length)),
        (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v))).natDegree *
          (Sig.get j).d ≤ (Sig.get j).a * (Sig.get j).d := by
      intro j _
      refine Nat.mul_le_mul_right _ ?_
      have := hT.2 k v (D.naut.locG (Sig.get j).π (D.naut.plGw k v))
      rwa [D.naut.locG_dim] at this
    intro j
    have := (Finset.sum_eq_sum_iff_of_le hle).1 hsum j (Finset.mem_univ j)
    exact Nat.eq_of_mul_eq_mul_right (hd j).2 this
  obtain ⟨hc, hall⟩ := Formalism.IrreducibleCountingLemmas.Z.good_cuspidal_multiplicity_one (ZMod (D.host.g k)) (D.nd.PlG k) D.R.r
    (fun v => D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v)))
    (Fin Sig.length) (fun j => (Sig.get j).a) (fun j => (Sig.get j).d)
    (fun v j => D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v))) hr
    (fun v => (h1 v).2.1) h2 hf hdeg (fun j => (hd j).1) (fun j => (hd j).2)
    (by
      rintro ⟨a, ha1, ha2, ha⟩
      obtain ⟨v, hv⟩ := h5 a ha1 ha2
      exact hv (ha v))
  rw [Fintype.card_fin] at hc
  obtain ⟨p, rfl⟩ := List.length_eq_one_iff.1 hc
  obtain ⟨hd1, ha1⟩ := hall ⟨0, by simp⟩
  obtain ⟨a, π, d⟩ := p
  simp only [List.get_eq_getElem, List.getElem_cons_zero] at hd1 ha1
  subst hd1 ha1
  exact ⟨π, rfl⟩

theorem eq_of_root_prod {K A : Type} [Field K] (s : Multiset A) (F : A → K) (a : K)
    (h : ((s.map fun x => X - C (F x)).prod).IsRoot a) : ∃ x ∈ s, F x = a := by
  rw [IsRoot, eval_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.map_map] at h
  obtain ⟨y, hy, e⟩ := Multiset.mem_map.1 h
  refine ⟨y, hy, ?_⟩
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C] at e
  exact (sub_eq_zero.1 e).symm

theorem isOfFinOrder_root {g : ℕ} [Fact g.Prime] {N : ℕ} {f : (ZMod g)[X]} (hf : Formalism.CyclotomicNorms.CycleTypeFiniteOrder.GoodPoly N f)
    {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ∈ Formalism.CyclotomicNorms.rootsBar f) : IsOfFinOrder x := by
  obtain ⟨r, σ, -, hmap, hσ⟩ := Formalism.CyclotomicNorms.CycleTypeFiniteOrder.exists_index hf
  rw [← hmap] at hx
  obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hx
  exact Formalism.CyclotomicNorms.CycleTypeFiniteOrder.isOfFinOrder_of_index hσ j (Formalism.CyclotomicNorms.CycleTypeFiniteOrder.ne_zero_of_mem hf (hmap ▸ Multiset.mem_map_of_mem _ (Finset.mem_univ_val j)))

theorem isOfFinOrder_alg {g : ℕ} [Fact g.Prime] (u : (ZMod g)ˣ) :
    IsOfFinOrder (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (u : ZMod g)) := by
  have hu : IsOfFinOrder u := isOfFinOrder_of_finite u
  exact (MonoidHom.isOfFinOrder ((algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).toMonoidHom.comp (Units.coeHom (ZMod g))) hu)

theorem primeToPart_inv {K : Type} [Field K] (ℓ : ℕ) (c : K) (hc : c ≠ 0) :
    Formalism.CyclotomicNorms.primeToPart ℓ c⁻¹ = (Formalism.CyclotomicNorms.primeToPart ℓ c)⁻¹ := by
  have ho : orderOf c⁻¹ = orderOf c := by
    let u : Kˣ := Units.mk0 c hc
    have h1 : (u : K) = c := rfl
    rw [← h1, ← Units.val_inv_eq_inv_val, orderOf_units, orderOf_units, orderOf_inv]
  unfold Formalism.CyclotomicNorms.primeToPart
  rw [ho, inv_pow]

theorem not_root_of {g ℓ : ℕ} [Fact g.Prime] [hℓ : Fact ℓ.Prime] (hℓg : ℓ ≠ g) {N : ℕ} {PP J : Type}
    (f : PP → (ZMod g)[X]) (χ : PP → J → (ZMod g)ˣ) (hG1 : Formalism.CyclotomicNorms.IsGood N g f χ)
    (hG2 : Formalism.CyclotomicNorms.IsGood N g f (fun v j => (χ v j)⁻¹)) (v : PP) (j : J)
    (ι : Formalism.CyclotomicNorms.Fbar g →* Formalism.CyclotomicNorms.Fbar ℓ)
    (hinj : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → (orderOf x).Coprime ℓ → (orderOf y).Coprime ℓ →
      ι x = ι y → x = y)
    (e₁ e₂ : ℤ) (he₁ : e₁ = 1 ∨ e₁ = -1) (he₂ : e₂ = 1 ∨ e₂ = -1) :
    ¬ (((Formalism.CyclotomicNorms.rootsBar (f v)).map fun x => X - C (ι (Formalism.CyclotomicNorms.primeToPart ℓ x) ^ e₁)).prod).IsRoot
      (ι (Formalism.CyclotomicNorms.primeToPart ℓ (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (χ v j : ZMod g))) ^ e₂) := by
  intro hroot
  obtain ⟨y, hy, hyeq⟩ := eq_of_root_prod _ (fun x => ι (Formalism.CyclotomicNorms.primeToPart ℓ x) ^ e₁) _ hroot
  obtain ⟨h1, h2, -, h3, -, -⟩ := hG1
  have h3' := hG2.2.2.2.1
  have gp : Formalism.CyclotomicNorms.CycleTypeFiniteOrder.GoodPoly N (f v) := ⟨(h1 v).1, (h1 v).2.1, (h1 v).2.2, h2 v⟩
  have hy0 := Formalism.CyclotomicNorms.CycleTypeFiniteOrder.ne_zero_of_mem gp hy
  have hyfin := isOfFinOrder_root gp hy
  set c := algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (χ v j : ZMod g) with hcdef
  have hc0 : c ≠ 0 := (_root_.map_ne_zero _).2 (χ v j).ne_zero
  have hcfin : IsOfFinOrder c := isOfFinOrder_alg (χ v j)
  have hcinv : c⁻¹ = algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (((χ v j)⁻¹ : (ZMod g)ˣ) : ZMod g) := by
    rw [hcdef, Units.val_inv_eq_inv_val, map_inv₀]
  have hcifin : IsOfFinOrder c⁻¹ := hcinv ▸ isOfFinOrder_alg (χ v j)⁻¹
  have ppne : ∀ z : Formalism.CyclotomicNorms.Fbar g, z ≠ 0 → Formalism.CyclotomicNorms.primeToPart ℓ z ≠ 0 := fun z hz => by
    unfold Formalism.CyclotomicNorms.primeToPart; exact pow_ne_zero _ hz
  have cop : ∀ z : Formalism.CyclotomicNorms.Fbar g, IsOfFinOrder z → (orderOf (Formalism.CyclotomicNorms.primeToPart ℓ z)).Coprime ℓ :=
    fun z hz => Formalism.CyclotomicNorms.CycleTypeFiniteOrder.primeToPart_coprime hℓ.out z hz
  have hιinv : ∀ z : Formalism.CyclotomicNorms.Fbar g, z ≠ 0 → ι z⁻¹ = (ι z)⁻¹ := fun z hz =>
    eq_inv_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel₀ hz, map_one])

  have case1 : ι (Formalism.CyclotomicNorms.primeToPart ℓ y) = ι (Formalism.CyclotomicNorms.primeToPart ℓ c) → False := fun e =>
    h3 ℓ hℓ.out hℓg v j y hy
      (hinj _ _ (ppne y hy0) (ppne c hc0) (cop y hyfin) (cop c hcfin) e)
  have case2 : ι (Formalism.CyclotomicNorms.primeToPart ℓ y) = (ι (Formalism.CyclotomicNorms.primeToPart ℓ c))⁻¹ → False := fun e => by
    rw [← hιinv _ (ppne c hc0), ← primeToPart_inv _ _ hc0] at e
    have := hinj _ _ (ppne y hy0) (ppne _ (inv_ne_zero hc0)) (cop y hyfin) (cop _ hcifin) e
    rw [hcinv] at this
    exact h3' ℓ hℓ.out hℓg v j y hy this
  rcases he₁ with rfl | rfl <;> rcases he₂ with rfl | rfl
  · simp only [zpow_one] at hyeq; exact case1 hyeq
  · simp only [zpow_one, zpow_neg] at hyeq; exact case2 hyeq
  · simp only [zpow_one, zpow_neg] at hyeq
    exact case2 (by rw [← hyeq, inv_inv])
  · simp only [zpow_neg, zpow_one, inv_inj] at hyeq; exact case1 hyeq

theorem theorem_three_prime_holds (D : D7) : ThreePrimeTheorem D := by
  rintro ⟨hT, hG⟩ hBB i Sig ⟨x, hx⟩ hdz hgood
  have hcusp := cusp_of D hT i x Sig hx hgood
  refine ⟨hcusp, fun ρ hρ => ?_⟩
  have hG' := hG i Sig ⟨x, hx⟩ hdz hcusp ρ hρ
  have hfact : ∀ j : Fin 2, Fact (D.host.g j).Prime := fun j => ⟨D.host.g_prime j⟩
  have hBB' : Formalism.CyclotomicNorms.BB D.R.r (D.host.g 0) ∩ Formalism.CyclotomicNorms.BB D.R.r (D.host.g 1) = ∅ :=
    Set.disjoint_iff_inter_eq_empty.mp hBB
  have hne : ∀ k : Fin 2, D.nd.l i ∉ Formalism.CyclotomicNorms.BB D.R.r (D.host.g k) → D.nd.l i ≠ D.host.g k :=
    fun k hk h => hk (Or.inl h)
  have key : ∀ k : Fin 2, D.nd.l i ∉ Formalism.CyclotomicNorms.BB D.R.r (D.host.g k) →
      Formalism.CyclotomicNorms.IrredOn (redF D i ρ) ⊤ ∧
      (∀ (H : Subgroup (G D.host.E D.nd.Om)) [H.Normal], Finite (G D.host.E D.nd.Om ⧸ H) →
        Group.IsSolvable (G D.host.E D.nd.Om ⧸ H) → (∀ v, D.ntypes.tg k v ∈ H) →
        Formalism.CyclotomicNorms.IrredOn (redF D i ρ) H) := by
    intro k hk
    have hA := (hG' k (hne k hk)).1
    choose ι hι using hA
    choose φ hφ using fun v => (hι v).2.2
    have T := Formalism.CyclotomicNorms.irreducibility_of_good_tuple D.R.r D.host.g D.nd.PlG (Fin D.R.m)
      (fun j v => D.naut.items₂ j (D.naut.plGw j v) (isoLoc D.nd D.naut Sig (D.naut.plGw j v)))
      D.nd.chiT hBB' (fun j => (hgood j).1) (D.nd.l i) k hk (G D.host.E D.nd.Om) (redF D i ρ)
      (fun v => D.ntypes.tg k v) φ ι hφ (fun v => (hι v).1) (fun v => (hι v).2.1)
    exact ⟨T.1, T.2.1⟩
  refine ⟨?_, ?_, ?_⟩
  · by_cases h0 : D.nd.l i ∈ Formalism.CyclotomicNorms.BB D.R.r (D.host.g 0)
    · have h1 : D.nd.l i ∉ Formalism.CyclotomicNorms.BB D.R.r (D.host.g 1) := fun h1 => by
        have hm : D.nd.l i ∈ Formalism.CyclotomicNorms.BB D.R.r (D.host.g 0) ∩ Formalism.CyclotomicNorms.BB D.R.r (D.host.g 1) := ⟨h0, h1⟩
        rw [hBB'] at hm
        exact hm
      exact (key 1 h1).1
    · exact (key 0 h0).1
  · intro k hk Hs _ hopen hsolv hIne
    have : Finite (G D.host.E D.nd.Om ⧸ Hs) := Subgroup.quotient_finite_of_isOpen Hs hopen
    exact (key k hk).2 Hs inferInstance hsolv
      (fun v => hIne _ (D.naut.plGw_over k v) (D.ntypes.tg_mem k v))
  · intro k hk w hw hTG
    obtain ⟨v, j, ι, e₁, e₂, he₁, he₂, hinj, hcp, hchi⟩ := (hG' k hk).2 w hw hTG
    show ¬ (Matrix.charpoly ((redF D i ρ (D.nd.gam0 i w) : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i)))).IsRoot _
    rw [hcp, hchi]
    exact not_root_of hk (fun v => D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v)))
      (D.nd.chiT k) (hgood k).1 (hgood k).2 v j ι hinj e₁ e₂ he₁ he₂

theorem residual_irreducible_of_theorem_three_prime (D : D7) (h : Adm3p D) (hAN : SumRepresentations.adm5 D) (hBN : LitBNIrr (G D.host.E D.nd.Om))
    (hrho : GlobalDatumResidualRepCondition D) (hdz : GlobalDatumDepthZeroCondition D) : ResidualIrreducibleRankR D :=
  residual_irreducible_of_theorem D (theorem_three_prime_holds D h) hAN hBN hrho hdz

end Formalism.MainNotions.AdmissibleThreePrime
