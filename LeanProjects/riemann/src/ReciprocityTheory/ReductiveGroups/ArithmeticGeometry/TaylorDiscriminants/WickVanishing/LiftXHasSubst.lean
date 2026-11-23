import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.GermSC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.WickFormula

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem liftX_hasSubst :
    HasSubst (fun p : Fin 1 × Fin d => (X (Sum.inl p.2) : AA k d)) := by
  first
  | exact hasSubst_of_constantCoeff_zero (fun p => by simp)
  | exact ⟨fun p => by simp, fun e => Set.toFinite _⟩

theorem liftX_add (f g : PS k 1 d) : liftX k (f + g) = liftX k f + liftX k g := MvPowerSeries.subst_add liftX_hasSubst f g

theorem liftX_mul (f g : PS k 1 d) : liftX k (f * g) = liftX k f * liftX k g := MvPowerSeries.subst_mul liftX_hasSubst f g

theorem Dof_add (F : Fin d → PS k 2 d) (u u' : Fin d → k) (f : PS k 1 d) :
    Dof F (u + u') f = Dof F u f + Dof F u' f := by
  unfold Dof
  simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem nabla_add (B : FB R d O) (h : PS k 2 d) (m : ℕ) (u u' φ φ' : Fin d → k) (G : AA k d) :
    nabla k B h m (u + u') (φ + φ') G = nabla k B h m u φ G + nabla k B h m u' φ' G := by
  first
  | (unfold nabla Dx
     simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, map_add, add_mul, mul_add, Finset.sum_add_distrib, Dof_add,
       liftX_add, smul_add, add_smul]
     ring)
  | (unfold nabla
     revert G u u' φ φ' m h B
     done)

def nablaL (B : FB R d O) (h : PS k 2 d) (m : ℕ) (u φ : Fin d → k) : Module.End k (AA k d) where
  toFun := nabla k B h m u φ
  map_add' G G' := by
    unfold nabla Dx
    simp only [map_add, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' c G := by
    unfold nabla Dx
    simp only [Derivation.map_smul, mul_smul_comm, RingHom.id_apply, smul_add, smul_sub, Finset.smul_sum]

@[simp] theorem nablaL_apply (B : FB R d O) (h : PS k 2 d) (m : ℕ) (u φ : Fin d → k) (G : AA k d) :
    nablaL B h m u φ G = nabla k B h m u φ G := rfl

theorem nablaL_add (B : FB R d O) (h : PS k 2 d) (m : ℕ) (u u' φ φ' : Fin d → k) :
    nablaL B h m (u + u') (φ + φ') = nablaL B h m u φ + nablaL B h m u' φ' := LinearMap.ext fun G => by
    simp only [LinearMap.add_apply, nablaL_apply]
    exact nabla_add B h m u u' φ φ' G

theorem nablaL_bracket (hN2 : ConnectionCommutator) (B : FB R d O) (h : PS k 2 d) (m : ℕ) (ξ η : (Fin d → k) × (Fin d → k)) :
    nablaL B h m ξ.1 ξ.2 * nablaL B h m η.1 η.2 - nablaL B h m η.1 η.2 * nablaL B h m ξ.1 ξ.2 =
      algebraMap k (Module.End k (AA k d)) ((m : k) * betaH k ξ η) := by
  unfold ConnectionCommutator at hN2
  apply LinearMap.ext
  intro G
  simp only [LinearMap.sub_apply, Module.End.mul_apply, nablaL_apply, Module.algebraMap_end_apply]
  first
  | exact hN2 B h m ξ η G
  | exact hN2 B h m ξ.1 ξ.2 η.1 η.2 G
  | exact hN2 B h m G ξ η
  | simpa using hN2 B h m ξ η G
  | simpa using hN2 B h m ξ.1 ξ.2 η.1 η.2 G
  | (apply hN2; done)
  | (simp only [Algebra.smul_def] at *; apply hN2; done)

theorem nablaL_comm (hN2 : ConnectionCommutator) (B : FB R d O) (h : PS k 2 d) (m : ℕ) (ξ η : (Fin d → k) × (Fin d → k))
    (hb : betaH k ξ η = 0) : Commute (nablaL B h m ξ.1 ξ.2) (nablaL B h m η.1 η.2) := by
  have hbr := nablaL_bracket hN2 B h m ξ η
  rw [hb, mul_zero, map_zero, sub_eq_zero] at hbr
  exact hbr

def sideE {ι : Type} [Fintype ι] (s : ι → Bool) :
    ι ≃ Fin (Fintype.card {l // s l = true}) ⊕ Fin (Fintype.card {l // ¬ s l = true}) :=
  (Equiv.sumCompl (fun l => s l = true)).symm.trans (Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _))

theorem sideE_symm_inl {ι : Type} [Fintype ι] (s : ι → Bool) (i : Fin (Fintype.card {l // s l = true})) :
    (sideE s).symm (Sum.inl i) = ((Fintype.equivFin {l // s l = true}).symm i).1 := rfl

theorem sideE_symm_inr {ι : Type} [Fintype ι] (s : ι → Bool) (j : Fin (Fintype.card {l // ¬ s l = true})) :
    (sideE s).symm (Sum.inr j) = ((Fintype.equivFin {l // ¬ s l = true}).symm j).1 := rfl

theorem side_inl {ι : Type} [Fintype ι] (s : ι → Bool) (i : Fin (Fintype.card {l // s l = true})) :
    s ((sideE s).symm (Sum.inl i)) = true := by
  rw [sideE_symm_inl]
  exact ((Fintype.equivFin {l // s l = true}).symm i).2

theorem side_inr {ι : Type} [Fintype ι] (s : ι → Bool) (j : Fin (Fintype.card {l // ¬ s l = true})) :
    s ((sideE s).symm (Sum.inr j)) = false := by
  rw [sideE_symm_inr]
  simpa using ((Fintype.equivFin {l // ¬ s l = true}).symm j).2

section Bridge

variable {ι : Type} [Fintype ι]

theorem foldr_eq_prod (f : ι → AA k d → AA k d) (F : ι → Module.End k (AA k d)) (hF : ∀ l, ⇑(F l) = f l)
    (n : ι →₀ ℕ) (L : List ι) (G : AA k d) :
    L.foldr (fun l g => (f l)^[n l] g) G = (L.map fun l => F l ^ n l).prod G := by
  induction L with
  | nil => simp
  | cons a L ih =>
    first
    | simp only [List.foldr_cons, List.map_cons, List.prod_cons, Module.End.mul_apply, Module.End.pow_apply, hF, ih]
    | simp only [List.foldr_cons, List.map_cons, List.prod_cons, LinearMap.mul_apply, LinearMap.pow_apply, hF, ih]

theorem perm_inl (s : ι → Bool) :
    ((Finset.univ : Finset ι).toList.filter (fun l => s l)).Perm
      (List.ofFn fun i => (sideE s).symm (Sum.inl i)) := by
  rw [List.perm_ext_iff_of_nodup ((Finset.nodup_toList _).filter _) ?_]
  · intro x
    simp only [List.mem_filter, Finset.mem_toList, Finset.mem_univ, true_and, List.mem_ofFn, Set.mem_range]
    constructor
    · intro hx
      exact ⟨Fintype.equivFin _ ⟨x, hx⟩, by rw [sideE_symm_inl]; simp⟩
    · rintro ⟨i, rfl⟩
      exact side_inl s i
  · rw [List.nodup_ofFn]
    intro i j hij
    simpa using congrArg (sideE s) hij

theorem perm_inr (s : ι → Bool) :
    ((Finset.univ : Finset ι).toList.filter (fun l => !s l)).Perm
      (List.ofFn fun j => (sideE s).symm (Sum.inr j)) := by
  rw [List.perm_ext_iff_of_nodup ((Finset.nodup_toList _).filter _) ?_]
  · intro x
    simp only [List.mem_filter, Finset.mem_toList, Finset.mem_univ, true_and, List.mem_ofFn, Set.mem_range,
      Bool.not_eq_true']
    constructor
    · intro hx
      exact ⟨Fintype.equivFin _ ⟨x, by simp [hx]⟩, by rw [sideE_symm_inr]; simp⟩
    · rintro ⟨j, rfl⟩
      exact side_inr s j
  · rw [List.nodup_ofFn]
    intro i j hij
    simpa using congrArg (sideE s) hij

theorem prod_perm_comm {A : Type} [Monoid A] {L L' : List A} (hp : L.Perm L')
    (hc : ∀ x ∈ L, ∀ y ∈ L, Commute x y) : L.prod = L'.prod := hp.prod_eq' (List.pairwise_of_forall_mem_list hc)

abbrev opL (B : FB R d O) (h : PS k 2 d) (m : ℕ) (s : ι → Bool) (ξ : ι → (Fin d → k) × (Fin d → k))
    (i : Fin (Fintype.card {l // s l = true})) : Module.End k (AA k d) :=
  nablaL B h m (ξ ((sideE s).symm (Sum.inl i))).1 (ξ ((sideE s).symm (Sum.inl i))).2

abbrev opR (B : FB R d O) (h : PS k 2 d) (m : ℕ) (s : ι → Bool) (ξ : ι → (Fin d → k) × (Fin d → k))
    (j : Fin (Fintype.card {l // ¬ s l = true})) : Module.End k (AA k d) :=
  nablaL B h m (ξ ((sideE s).symm (Sum.inr j))).1 (ξ ((sideE s).symm (Sum.inr j))).2

theorem ordNabla_eq (B : FB R d O) (h : PS k 2 d) (m : ℕ) (s : ι → Bool) (ξ : ι → (Fin d → k) × (Fin d → k))
    (hc : ∀ l l', s l = s l' → Commute (nablaL B h m (ξ l).1 (ξ l).2) (nablaL B h m (ξ l').1 (ξ l').2))
    (P : MvPolynomial ι k) (G : AA k d) :
    ordNabla k B h m s ξ P G =
      PI.WickFormula.ordEval (opL B h m s ξ) (opR B h m s ξ) (MvPolynomial.rename (sideE s) P) G := by
  classical
  set F : ι → Module.End k (AA k d) := fun l => nablaL B h m (ξ l).1 (ξ l).2 with hFdef
  unfold ordNabla PI.WickFormula.ordEval
  rw [LinearMap.sum_apply, MvPolynomial.support_rename_of_injective (sideE s).injective,
    Finset.sum_image (fun x _ y _ hxy => Finsupp.mapDomain_injective (sideE s).injective hxy)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [MvPolynomial.coeff_rename_mapDomain _ (sideE s).injective, LinearMap.smul_apply, smul_eq_C_mul,
    Module.End.mul_apply]
  congr 1
  rw [foldr_eq_prod (fun l => nabla k B h m (ξ l).1 (ξ l).2) F (fun _ => rfl) n,
    foldr_eq_prod (fun l => nabla k B h m (ξ l).1 (ξ l).2) F (fun _ => rfl) n]
  simp only [Finsupp.mapDomain_equiv_apply]
  have hS : (((Finset.univ : Finset ι).toList.filter (fun l => s l)).map fun l => F l ^ n l).prod =
      (List.ofFn fun i => opL B h m s ξ i ^ n ((sideE s).symm (Sum.inl i))).prod := by
    rw [show (fun i => opL B h m s ξ i ^ n ((sideE s).symm (Sum.inl i))) =
      (fun l => F l ^ n l) ∘ (fun i => (sideE s).symm (Sum.inl i)) from rfl, ← List.map_ofFn]
    refine prod_perm_comm ((perm_inl s).map _) ?_
    intro x hx y hy
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
    obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hy
    have e : s l = s l' := by
      rw [(List.mem_filter.mp hl).2, (List.mem_filter.mp hl').2]
    exact (hc l l' e).pow_pow _ _
  have hC : (((Finset.univ : Finset ι).toList.filter (fun l => !s l)).map fun l => F l ^ n l).prod =
      (List.ofFn fun j => opR B h m s ξ j ^ n ((sideE s).symm (Sum.inr j))).prod := by
    rw [show (fun j => opR B h m s ξ j ^ n ((sideE s).symm (Sum.inr j))) =
      (fun l => F l ^ n l) ∘ (fun j => (sideE s).symm (Sum.inr j)) from rfl, ← List.map_ofFn]
    refine prod_perm_comm ((perm_inr s).map _) ?_
    intro x hx y hy
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
    obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hy
    have e : s l = s l' := by
      have a := (List.mem_filter.mp hl).2
      have b := (List.mem_filter.mp hl').2
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at a b
      rw [a, b]
    exact (hc l l' e).pow_pow _ _
  rw [hS, hC]

end Bridge

end ReciprocityTheory.ChartRestriction.G.TB.SCPf
