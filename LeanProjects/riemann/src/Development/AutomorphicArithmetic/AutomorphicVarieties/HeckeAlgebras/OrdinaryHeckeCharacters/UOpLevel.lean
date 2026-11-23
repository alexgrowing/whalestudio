import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IwMemMul
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem uOpLevel_mem {G : Type} [Group G] (I : Iwa G) (a x : G) :
    x ∈ I.Nconj a ↔ a⁻¹ * x * a ∈ I.N := by
  constructor
  · intro h
    obtain ⟨n, hn, e⟩ := Subgroup.mem_map.1 h
    have e2 : a * n * a⁻¹ = x := e
    have : a⁻¹ * x * a = n := by rw [← e2]; group
    rwa [this]
  · intro h
    refine Subgroup.mem_map.2 ⟨_, h, ?_⟩
    show a * (a⁻¹ * x * a) * a⁻¹ = x
    group

private theorem uOpLevel_core {G : Type} [Group G] (I : Iwa G) {A M : Type} [CommRing A] [AddCommGroup M]
    [Module A M] (π : Representation A G M) (c : ℕ) {a : G} (ha : a ∈ I.P) {v : M} (hN : v ∈ fixd π I.N)
    (hT : v ∈ fixd π (I.Tc c)) (hm : ∀ y ∈ I.Nm c, π (a⁻¹ * y * a) v = v) :
    I.uOp π a v ∈ fixd π (I.Nm c) := by
  classical
  intro y hy
  have mul : ∀ (g h : G) (w : M), π (g * h) w = π g (π h w) := fun g h w => by
    rw [map_mul π g h, Module.End.mul_apply]
  obtain ⟨⟨s, hs, hu⟩, h2⟩ := uOpSum G I A M π a ha
  have key : ∀ u : s, ∃ u' : s, ∃ k ∈ I.Iw c, π k v = v ∧ y * (u * a) = u' * a * k := by
    intro u
    obtain ⟨x, hx, t, ht, y', hy', e⟩ := I.swap c y hy u (hs _ u.2)
    obtain ⟨u', ⟨hu', hx'⟩, -⟩ := hu x hx
    rw [uOpLevel_mem] at hx'
    have hc : t * a = a * t := I.comm t (I.T_le (I.Tc_le c ht)) a (I.P_le a ha)
    refine ⟨⟨u', hu'⟩, (a⁻¹ * (u'⁻¹ * x) * a) * t * (a⁻¹ * y' * a),
      (iwMem G I c _).1.2 ⟨_, hx', t, I.Tc_le c ht, _, I.P_Nm c a ha y' hy', rfl⟩, ?_, ?_⟩
    · rw [mul, hm y' hy', mul, hT t ht, hN _ hx']
    · have h2 : t = a * t * a⁻¹ := by rw [← hc]; group
      calc y * (u * a) = (y * u) * a := by group
        _ = x * (a * t * a⁻¹) * y' * a := by rw [e, ← h2]
        _ = _ := by simp only []; group
  choose σ k hk hkv he using key
  have inj : Function.Injective σ := by
    intro u w h
    have e : a⁻¹ * ((u : G)⁻¹ * w) * a = (k u)⁻¹ * k w := by
      calc a⁻¹ * ((u : G)⁻¹ * w) * a = (y * (u * a))⁻¹ * (y * (w * a)) := by group
        _ = _ := by rw [he u, he w, h]; group
    have h1 : a⁻¹ * ((u : G)⁻¹ * w) * a ∈ I.Nf := by
      simpa using I.Tf_Nf a⁻¹ (inv_mem (I.P_le a ha)) _
        (I.N_le (mul_mem (inv_mem (hs _ u.2)) (hs _ w.2)))
    have h3 := (iwMem G I c _).2.2 h1 (e ▸ mul_mem (inv_mem (hk u)) (hk w))
    exact Subtype.ext ((hu w (hs _ w.2)).unique ⟨u.2, (uOpLevel_mem I a _).2 h3⟩ ⟨w.2, by simp⟩)
  rw [(h2 s hs hu).2 v hN, map_sum, ← Finset.sum_coe_sort s, ← Finset.sum_coe_sort s,
    ← (Finite.injective_iff_bijective.1 inj).sum_comp (fun u : s => π (u * a) v)]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← mul, he u, mul, hkv u]

private theorem fixed_pro_unipotent_iff {G : Type} [Group G] (I : Iwa G) {A M : Type} [CommRing A] [AddCommGroup M]
    [Module A M] (π : Representation A G M) (c : ℕ) (v : M) :
    v ∈ fixd π (I.I1 c) ↔ v ∈ fixd π I.N ∧ v ∈ fixd π (I.Tc c) ∧ v ∈ fixd π (I.Nm c) := by
  constructor
  · intro h
    exact ⟨fun u hu => h u (Subgroup.mem_sup_left (Subgroup.mem_sup_left hu)),
      fun u hu => h u (Subgroup.mem_sup_left (Subgroup.mem_sup_right hu)),
      fun u hu => h u (Subgroup.mem_sup_right hu)⟩
  · rintro ⟨h1, h2, h3⟩ g hg
    obtain ⟨x, hx, t, ht, y, hy, rfl⟩ := (iwMem G I c g).2.1.1 hg
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h3 y hy, h2 t ht, h1 x hx]

theorem UpperTheory.V.Hi.uOpLevel :
    ∀ (G : Type) [Group G] (I : Iwa G) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (π : Representation A G M) (c : ℕ), (∀ a ∈ I.P, ∀ v ∈ fixd π (I.I1 c), I.uOp π a v ∈ fixd π (I.I1 c)) ∧ (∀ v, v ∈ fixd π I.N → v ∈ fixd π (I.Tc c) → v ∈ fixd π (I.Nm (c + 1)) → I.uOp π I.z v ∈ fixd π (I.I1 c)) ∧ ∀ φ : I.T →* Aˣ, (∀ t : I.T, (t : G) ∈ I.Tc c → φ t = 1) → (∀ a ∈ I.P, ∀ v ∈ I.eig π c φ, I.uOp π a v ∈ I.eig π c φ) ∧ ∀ v ∈ I.eig π (c + 1) φ, I.uOp π I.z v ∈ I.eig π c φ := by
  intro G _ I A M _ _ _ π c
  have gen : ∀ a ∈ I.P, ∀ v, v ∈ fixd π I.N → v ∈ fixd π (I.Tc c) → (∀ y ∈ I.Nm c, π (a⁻¹ * y * a) v = v) →
      I.uOp π a v ∈ fixd π (I.I1 c) := by
    intro a ha v hN hT hm
    obtain ⟨h1, -, -, h2, -⟩ := uOpMul G I A M π a a ha ha v hN
    exact (fixed_pro_unipotent_iff I π c _).2 ⟨h1, fun t ht => by rw [h2 t (I.Tc_le c ht), hT t ht],
      uOpLevel_core I π c ha hN hT hm⟩
  refine ⟨fun a ha v hv => ?_, fun v hN hT hm => gen _ I.z_mem v hN hT fun y hy => hm _ (I.z_Nm c y hy),
    fun φ hφ => ?_⟩
  · obtain ⟨hN, hT, hm⟩ := (fixed_pro_unipotent_iff I π c v).1 hv
    exact gen a ha v hN hT fun y hy => hm _ (I.P_Nm c a ha y hy)
  · have gen' : ∀ a ∈ I.P, ∀ v, v ∈ fixd π I.N → (∀ t : I.T, π t v = (((φ t)⁻¹ : Aˣ) : A) • v) →
        (∀ y ∈ I.Nm c, π (a⁻¹ * y * a) v = v) → I.uOp π a v ∈ I.eig π c φ := by
      intro a ha v hN hT hm
      have hT' : v ∈ fixd π (I.Tc c) := fun t ht => by
        have := hT ⟨t, I.Tc_le c ht⟩
        rw [hφ _ ht] at this
        simpa using this
      obtain ⟨h1, -, -, h2, -⟩ := uOpMul G I A M π a a ha ha v hN
      exact ⟨h1, uOpLevel_core I π c ha hN hT' hm, fun t => by rw [h2 t t.2, hT t, map_smul]⟩
    exact ⟨fun a ha v hv => gen' a ha v hv.1 hv.2.2 fun y hy => hv.2.1 _ (I.P_Nm c a ha y hy),
      fun v hv => gen' _ I.z_mem v hv.1 hv.2.2 fun y hy => hv.2.1 _ (I.z_Nm c y hy)⟩
