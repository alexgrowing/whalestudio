import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PiPtsHecke

open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Hi

section
variable {H Y Z : Type} {I : Type 1} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]

private theorem span_push (σ : I → SmIrr H) (π : Representation ℂ H Y) (ρ : Representation ℂ H Z)
    (p : Y →ₗ[ℂ] Z) (hp : Function.Surjective p) (he : ∀ g v, p (π g v) = ρ g (p v))
    (hs : ∀ y, y ∈ ⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] Y // ∀ g v, f ((σ i).ρ g v) = π g (f v)}), LinearMap.range f.1) :
    ∀ z, z ∈ ⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] Z // ∀ g v, f ((σ i).ρ g v) = ρ g (f v)}), LinearMap.range f.1 := by
  intro z
  obtain ⟨y, rfl⟩ := hp z
  have hle : (⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] Y // ∀ g v, f ((σ i).ρ g v) = π g (f v)}), LinearMap.range f.1) ≤
      (⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] Z // ∀ g v, f ((σ i).ρ g v) = ρ g (f v)}), LinearMap.range f.1).comap p := by
    refine iSup_le fun i => iSup_le fun f => ?_
    rintro _ ⟨v, rfl⟩
    have h : LinearMap.range (p ∘ₗ f.1) ≤
        ⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] Z // ∀ g v, f ((σ i).ρ g v) = ρ g (f v)}), LinearMap.range f.1 :=
      le_iSup_of_le i (le_iSup_of_le
        (⟨p ∘ₗ f.1, fun g v => by simp only [LinearMap.comp_apply]; rw [f.2 g v, he]⟩ :
          {f : (σ i).V →ₗ[ℂ] Z // ∀ g v, f ((σ i).ρ g v) = ρ g (f v)}) le_rfl)
    exact h ⟨v, rfl⟩
  exact hle (hs y)

private theorem iso_push (τ : SmIrr H) (π : Representation ℂ H Y) (ρ : Representation ℂ H Z)
    (p : Y →ₗ[ℂ] Z) (hp : Function.Surjective p) (he : ∀ g v, p (π g v) = ρ g (p v))
    (h : IsoSum π ⊤ τ) : IsoSum ρ ⊤ τ := by
  intro z _
  obtain ⟨y, rfl⟩ := hp z
  have hle : (⨆ f : {f : τ.V →ₗ[ℂ] Y // (∀ g v, f (τ.ρ g v) = π g (f v)) ∧ LinearMap.range f ≤ ⊤}, LinearMap.range f.1) ≤
      (⨆ f : {f : τ.V →ₗ[ℂ] Z // (∀ g v, f (τ.ρ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ ⊤}, LinearMap.range f.1).comap p := by
    refine iSup_le fun f => ?_
    rintro _ ⟨v, rfl⟩
    have h' : LinearMap.range (p ∘ₗ f.1) ≤
        ⨆ f : {f : τ.V →ₗ[ℂ] Z // (∀ g v, f (τ.ρ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ ⊤}, LinearMap.range f.1 :=
      le_iSup_of_le
        (⟨p ∘ₗ f.1, fun g v => by simp only [LinearMap.comp_apply]; rw [f.2.1 g v, he], le_top⟩ :
          {f : τ.V →ₗ[ℂ] Z // (∀ g v, f (τ.ρ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ ⊤}) le_rfl
    exact h' ⟨v, rfl⟩
  exact hle (h Submodule.mem_top)

private theorem iso_quot (σ : I → SmIrr H) (π : Representation ℂ H Y) (ρ : Representation ℂ H Z)
    (p : Y →ₗ[ℂ] Z) (hp : Function.Surjective p) (he : ∀ g v, p (π g v) = ρ g (p v))
    (hs : ∀ y, y ∈ ⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] Y // ∀ g v, f ((σ i).ρ g v) = π g (f v)}), LinearMap.range f.1)
    (i₀ : I)
    (hk : (⨆ (i : {i : I // IsEmpty ((σ i₀).ρ.Equiv (σ i).ρ)})
      (f : {f : (σ i.1).V →ₗ[ℂ] Y // ∀ g v, f ((σ i.1).ρ g v) = π g (f v)}), LinearMap.range f.1) ≤ LinearMap.ker p) :
    IsoSum ρ ⊤ (σ i₀) := by
  intro z _
  obtain ⟨y, rfl⟩ := hp z
  have hle : (⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] Y // ∀ g v, f ((σ i).ρ g v) = π g (f v)}), LinearMap.range f.1) ≤
      (⨆ f : {f : (σ i₀).V →ₗ[ℂ] Z // (∀ g v, f ((σ i₀).ρ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ ⊤}, LinearMap.range f.1).comap p := by
    refine iSup_le fun i => iSup_le fun f => ?_
    rintro _ ⟨v, rfl⟩
    by_cases hi : IsEmpty ((σ i₀).ρ.Equiv (σ i).ρ)
    · have h0 : f.1 v ∈ LinearMap.ker p :=
        hk (Submodule.mem_iSup_of_mem ⟨i, hi⟩ (Submodule.mem_iSup_of_mem ⟨f.1, f.2⟩ ⟨v, rfl⟩))
      rw [Submodule.mem_comap, LinearMap.mem_ker.1 h0]
      exact Submodule.zero_mem _
    · obtain ⟨e⟩ := not_isEmpty_iff.1 hi
      have h' : LinearMap.range (p ∘ₗ f.1 ∘ₗ e.toLinearEquiv.toLinearMap) ≤
          ⨆ f : {f : (σ i₀).V →ₗ[ℂ] Z // (∀ g v, f ((σ i₀).ρ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ ⊤}, LinearMap.range f.1 :=
        le_iSup_of_le
          (⟨p ∘ₗ f.1 ∘ₗ e.toLinearEquiv.toLinearMap, fun g v => by
            have h1 := (congrArg f.1 (e.toIntertwiningMap.isIntertwining _ _ g v)).trans (f.2 g _)
            exact (congrArg p h1).trans (he g _), le_top⟩ :
            {f : (σ i₀).V →ₗ[ℂ] Z // (∀ g v, f ((σ i₀).ρ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ ⊤}) le_rfl
      refine h' ⟨e.toLinearEquiv.symm v, ?_⟩
      exact congrArg (fun w => p (f.1 w)) (e.toLinearEquiv.apply_symm_apply v)
  exact hle (hs y)

end

private theorem stab_N {Q : Type} [Finite Q] [DecidableEq Q] {H : Q → Type} [∀ q, Group (H q)]
    {Y : Type} {I : Type 1} [AddCommGroup Y] [Module ℂ Y] (q : Q) (V : I → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] (τ : ∀ i, Representation ℂ (H q) (V i))
    (π : Representation ℂ (∀ q, H q) Y) (P : I → Prop) (g : ∀ q, H q) :
    (⨆ (i : {i : I // P i}) (f : {f : V i.1 →ₗ[ℂ] Y // ∀ h v, f (τ i.1 h v) = π (Pi.mulSingle q h) (f v)}),
      LinearMap.range f.1) ≤
    (⨆ (i : {i : I // P i}) (f : {f : V i.1 →ₗ[ℂ] Y // ∀ h v, f (τ i.1 h v) = π (Pi.mulSingle q h) (f v)}),
      LinearMap.range f.1).comap (π g) := by
  set N : Submodule ℂ Y := ⨆ (i : {i : I // P i})
    (f : {f : V i.1 →ₗ[ℂ] Y // ∀ h v, f (τ i.1 h v) = π (Pi.mulSingle q h) (f v)}), LinearMap.range f.1 with hN
  let S : Submonoid (∀ q, H q) :=
    { carrier := {g | N ≤ N.comap (π g)}
      one_mem' := fun n hn => by simpa using hn
      mul_mem' := fun {a b} ha hb n hn => by
        have : π (a * b) n = π a (π b n) := by rw [map_mul]; rfl
        rw [Submodule.mem_comap, this]
        exact ha (hb hn) }
  refine Submonoid.pi_mem_of_mulSingle_mem (H := S) g fun q' => ?_
  show N ≤ N.comap (π (Pi.mulSingle q' (g q')))
  refine iSup_le fun i => iSup_le fun f => ?_
  rintro _ ⟨v, rfl⟩
  by_cases hq : q' = q
  · subst hq
    rw [Submodule.mem_comap, ← f.2 (g q') v]
    exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem f ⟨_, rfl⟩)
  · have hc : ∀ (h : H q) (x : Y), π (Pi.mulSingle q' (g q')) (π (Pi.mulSingle q h) x) =
        π (Pi.mulSingle q h) (π (Pi.mulSingle q' (g q')) x) := fun h x => by
      have h1 : π (Pi.mulSingle q' (g q') * Pi.mulSingle q h) x = π (Pi.mulSingle q h * Pi.mulSingle q' (g q')) x := by
        rw [(Pi.mulSingle_commute hq (g q') h).eq]
      rw [map_mul, map_mul] at h1
      exact h1
    exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem
      ⟨π (Pi.mulSingle q' (g q')) ∘ₗ f.1, fun h w => by
        simp only [LinearMap.comp_apply]
        rw [f.2 h w, hc]⟩ ⟨v, rfl⟩)

theorem UpperTheory.GalN.V.isoRefine :
        (∀ (H Y : Type) (I : Type 1) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup Y] [Module ℂ Y] (σ : I → SmIrr H) (π : Representation ℂ H Y), (∀ y, y ∈ ⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] Y // ∀ g v, f ((σ i).ρ g v) = π g (f v)}), LinearMap.range f.1) → ∀ y : Y, y ≠ 0 → ∃ i₀ : I, y ∉ ⨆ (i : {i : I // IsEmpty ((σ i₀).ρ.Equiv (σ i).ρ)}) (f : {f : (σ i.1).V →ₗ[ℂ] Y // ∀ g v, f ((σ i.1).ρ g v) = π g (f v)}), LinearMap.range f.1) → ∀ (Q : Type) [Finite Q] [DecidableEq Q] (H : Q → Type) [∀ q, Group (H q)] [∀ q, TopologicalSpace (H q)] [∀ q, IsTopologicalGroup (H q)] (Y : Type) (I : Type 1) [AddCommGroup Y] [Module ℂ Y] (σ : I → ∀ q, SmIrr (H q)) (π : Representation ℂ (∀ q, H q) Y), (∀ q y, y ∈ ⨆ (i : I) (f : {f : (σ i q).V →ₗ[ℂ] Y // ∀ g v, f ((σ i q).ρ g v) = π (Pi.mulSingle q g) (f v)}), LinearMap.range f.1) → ∀ y : Y, y ≠ 0 → ∃ (Y' : Type) (_ : AddCommGroup Y') (_ : Module ℂ Y') (π' : Representation ℂ (∀ q, H q) Y') (p : Y →ₗ[ℂ] Y') (c : Q → I), p y ≠ 0 ∧ (∀ g v, p (π g v) = π' g (p v)) ∧ ∀ q, IsoSum (π'.comp (MonoidHom.mulSingle H q)) ⊤ (σ (c q) q) := by
  intro hPick Q _ _ H _ _ _ Y I _ _ σ π hs y hy
  haveI := Fintype.ofFinite Q
  have key : ∀ T : Finset Q, ∃ (Y' : Type) (_ : AddCommGroup Y') (_ : Module ℂ Y')
      (π' : Representation ℂ (∀ q, H q) Y') (p : Y →ₗ[ℂ] Y') (c : Q → I),
      Function.Surjective p ∧ p y ≠ 0 ∧ (∀ g v, p (π g v) = π' g (p v)) ∧
      (∀ q ∈ T, IsoSum (π'.comp (MonoidHom.mulSingle H q)) ⊤ (σ (c q) q)) ∧
      (∀ q y, y ∈ ⨆ (i : I) (f : {f : (σ i q).V →ₗ[ℂ] Y' // ∀ g v, f ((σ i q).ρ g v) = π' (Pi.mulSingle q g) (f v)}), LinearMap.range f.1) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      exact ⟨Y, _, _, π, LinearMap.id,
        fun q => (hPick (H q) Y I (fun i => σ i q) (π.comp (MonoidHom.mulSingle H q)) (hs q) y hy).choose,
        Function.surjective_id, hy, fun _ _ => rfl, by simp, hs⟩
    | insert q T hq ih =>
      obtain ⟨Y', _, _, π', p, c, hsurj, hpy, he, hiso, hsp⟩ := ih
      obtain ⟨i₀, hi₀⟩ := hPick (H q) Y' I (fun i => σ i q) (π'.comp (MonoidHom.mulSingle H q)) (hsp q) (p y) hpy
      set N : Submodule ℂ Y' := ⨆ (i : {i : I // IsEmpty ((σ i₀ q).ρ.Equiv (σ i q).ρ)})
        (f : {f : (σ i.1 q).V →ₗ[ℂ] Y' // ∀ g v, f ((σ i.1 q).ρ g v) = π' (Pi.mulSingle q g) (f v)}),
        LinearMap.range f.1 with hNdef
      have hi₀' : p y ∉ N := hi₀
      have hN : ∀ g, N ≤ N.comap (π' g) := fun g =>
        stab_N q (fun i => (σ i q).V) (fun i => (σ i q).ρ) π' (fun i => IsEmpty ((σ i₀ q).ρ.Equiv (σ i q).ρ)) g
      have hmk : ∀ g v, N.mkQ (π' g v) = π'.quotient N hN g (N.mkQ v) := fun g v => rfl
      refine ⟨Y' ⧸ N, inferInstance, inferInstance, π'.quotient N hN, N.mkQ ∘ₗ p, Function.update c q i₀,
        (N.mkQ_surjective).comp hsurj, ?_, ?_, ?_, ?_⟩
      · simpa using hi₀'
      · intro g v
        simp only [LinearMap.comp_apply]
        rw [he, hmk]
      · intro q' hq'
        rcases Finset.mem_insert.1 hq' with rfl | hq'
        · rw [Function.update_self]
          exact iso_quot (fun i => σ i q') (π'.comp (MonoidHom.mulSingle H q'))
            ((π'.quotient N hN).comp (MonoidHom.mulSingle H q')) N.mkQ N.mkQ_surjective
            (fun g v => hmk _ v) (hsp q') i₀ (by rw [Submodule.ker_mkQ]; exact le_rfl)
        · have hne : q' ≠ q := fun h => hq (h ▸ hq')
          rw [Function.update_of_ne hne]
          exact iso_push _ (π'.comp (MonoidHom.mulSingle H q'))
            ((π'.quotient N hN).comp (MonoidHom.mulSingle H q')) N.mkQ N.mkQ_surjective
            (fun g v => hmk _ v) (hiso q' hq')
      · intro q'
        exact span_push (fun i => σ i q') (π'.comp (MonoidHom.mulSingle H q'))
          ((π'.quotient N hN).comp (MonoidHom.mulSingle H q')) N.mkQ N.mkQ_surjective
          (fun g v => hmk _ v) (hsp q')
  obtain ⟨Y', i1, i2, π', p, c, -, hpy, he, hiso, -⟩ := key Finset.univ
  exact ⟨Y', i1, i2, π', p, c, hpy, he, fun q => hiso q (Finset.mem_univ q)⟩
