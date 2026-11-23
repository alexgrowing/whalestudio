import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.TcAnti
open Matrix UpperTheory.V.Hi

private theorem piRel {σ : Type} [Finite σ] {G : σ → Type} [∀ v, Group (G v)] (H K : ∀ v, Subgroup (G v))
    (h : ∀ v, (H v).relIndex (K v) ≠ 0) :
    (Subgroup.pi Set.univ H).relIndex (Subgroup.pi Set.univ K) ≠ 0 := by
  let φ : ∀ v, (Subgroup.pi Set.univ K) →* K v := fun v =>
    { toFun := fun x => ⟨x.1 v, x.2 v trivial⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have e : (Subgroup.pi Set.univ H).subgroupOf (Subgroup.pi Set.univ K) =
      ⨅ v, ((H v).subgroupOf (K v)).comap (φ v) := by
    ext x
    rw [Subgroup.mem_iInf]
    exact ⟨fun h v => h v trivial, fun h v _ => h v⟩
  rw [Subgroup.relIndex, e]
  refine Subgroup.index_iInf_ne_zero fun v => ?_
  rw [Subgroup.index_comap]
  exact fun h0 => h v (Subgroup.index_eq_zero_of_relIndex_eq_zero h0)

private theorem exhMono {G : Type} [Group G] (I : Iwa G) {x : G} {k m : ℕ} (hkm : k ≤ m)
    (h : I.z ^ k * x * (I.z ^ k)⁻¹ ∈ I.N) : I.z ^ m * x * (I.z ^ m)⁻¹ ∈ I.N := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hkm
  have := I.P_N _ (I.P.pow_mem I.z_mem d) _ h
  convert this using 1
  rw [pow_add]; group

private theorem divMono {G : Type} [Group G] (I : Iwa G) {a : G} {k m : ℕ} (hkm : k ≤ m)
    (h : I.z ^ k * a⁻¹ ∈ I.P) : I.z ^ m * a⁻¹ ∈ I.P := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hkm
  rw [pow_add, mul_assoc]
  exact I.P.mul_mem (I.P.pow_mem I.z_mem d) h

theorem UpperTheory.V.Hi.piAx :
    ∀ (σ : Type) [Finite σ] (G : σ → Type) [∀ v, Group (G v)] (I : ∀ v, Iwa (G v)), (piData I).Ax := by
  intro σ _ G _ I
  refine
    { N_le := fun x hx v hv => (I v).N_le (hx v hv)
      T_le := fun x hx v hv => (I v).T_le (hx v hv)
      P_le := fun x hx v hv => (I v).P_le _ (hx v hv)
      z_mem := fun v _ => (I v).z_mem
      Tc_le := fun c x hx v hv => (I v).Tc_le c (hx v hv)
      Tc_anti := fun c d h x hx v hv => (I v).Tc_anti h (hx v hv)
      Nm_anti := fun c d h x hx v hv => (I v).Nm_anti h (hx v hv)
      comm := fun s hs t ht => funext fun v => (I v).comm _ (hs v trivial) _ (ht v trivial)
      Tf_Nf := fun s hs t ht v hv => (I v).Tf_Nf _ (hs v hv) _ (ht v hv)
      T_N := fun s hs t ht v hv => (I v).T_N _ (hs v hv) _ (ht v hv)
      T_Nm := fun c s hs t ht v hv => (I v).T_Nm c _ (hs v hv) _ (ht v hv)
      P_N := fun s hs t ht v hv => (I v).P_N _ (hs v hv) _ (ht v hv)
      P_Nm := fun c s hs t ht v hv => (I v).P_Nm c _ (hs v hv) _ (ht v hv)
      z_Nm := fun c t ht v hv => (I v).z_Nm c _ (ht v hv)
      swap := ?_
      uniq := ?_
      fin_N := ?_
      fin_Nm := fun c => piRel _ _ fun v => (I v).fin_Nm c
      fin_Tc := fun c => piRel _ _ fun v => (I v).fin_Tc c
      exh := ?_
      exists_pow_mul_inv_mem := ?_
      gen := ?_ }
  · intro c y hy x hx
    choose x' hx' t ht y' hy' e using fun v => (I v).swap c _ (hy v trivial) _ (hx v trivial)
    exact ⟨x', fun v _ => hx' v, t, fun v _ => ht v, y', fun v _ => hy' v, funext e⟩
  · intro x hx t ht y hy e
    have h := fun v => (I v).uniq _ (hx v trivial) _ (ht v trivial) _ (hy v trivial) (congrFun e v)
    exact ⟨funext fun v => (h v).1, funext fun v => (h v).2⟩
  · intro a ha
    have e : (piData I).N.map (MulAut.conj a).toMonoidHom =
        Subgroup.pi Set.univ fun v => (I v).N.map (MulAut.conj (a v)).toMonoidHom := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩ v hv
        exact ⟨y v, hy v hv, rfl⟩
      · intro h
        choose y hy e using fun v => h v trivial
        exact ⟨y, fun v _ => hy v, funext e⟩
    rw [e]
    exact piRel _ _ fun v => (I v).fin_N _ (ha v trivial)
  · intro x hx
    choose k hk using fun v => (I v).exh _ (hx v trivial)
    obtain ⟨m, hm⟩ := (Set.finite_range k).bddAbove
    exact ⟨m, fun v _ => exhMono (I v) (hm ⟨v, rfl⟩) (hk v)⟩
  · intro a ha
    choose k hk using fun v => (I v).exists_pow_mul_inv_mem _ (ha v trivial)
    obtain ⟨m, hm⟩ := (Set.finite_range k).bddAbove
    exact ⟨m, fun v _ => divMono (I v) (hm ⟨v, rfl⟩) (hk v)⟩
  · intro t ht
    choose s hs a ha b hb e using fun v => (I v).gen _ (ht v trivial)
    exact ⟨s, fun v _ => hs v, a, fun v _ => ha v, b, fun v _ => hb v, funext e⟩
