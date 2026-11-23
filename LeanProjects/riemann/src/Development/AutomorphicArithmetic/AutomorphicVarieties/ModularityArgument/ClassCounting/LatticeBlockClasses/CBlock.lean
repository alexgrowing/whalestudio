import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.MemPowEqv

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

section

variable {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] {J X : Type}

omit [NumberField L] [NumberField F] in
private theorem blk_apply {g : GG L F J} {s : J → F ≃ₐ[L] F} {β : J → X}
    {g' : ∀ x : X, ({j // β j = x} → F) ≃ₗ[F] ({j // β j = x} → F)} (h : BlockForm g s β g') (w : J → F) (x : X)
    (i : {j // β j = x}) : s i.1 (g w i.1) = g' x (fun i => s i.1 (w i.1)) i := by
  obtain ⟨j, rfl⟩ := i
  exact h w j

omit [NumberField L] [NumberField F] in
private theorem blk_glue {β : J → X} (f : ∀ x : X, ({j // β j = x} → F)) (x : X) :
    (fun i : {j // β j = x} => f (β i.1) ⟨i.1, rfl⟩) = f x := by
  funext i
  obtain ⟨j, hj⟩ := i
  subst hj
  rfl

omit [NumberField L] [NumberField F] in
private theorem blk_exists (s : J → F ≃ₐ[L] F) (β : J → X)
    (g' : ∀ x : X, ({j // β j = x} → F) ≃ₗ[F] ({j // β j = x} → F)) : ∃ g : GG L F J, BlockForm g s β g' := by
  let G : (J → F) ≃ₗ[F] (J → F) :=
    { toFun := fun v j => g' (β j) (fun i => v i.1) ⟨j, rfl⟩
      invFun := fun v j => (g' (β j)).symm (fun i => v i.1) ⟨j, rfl⟩
      map_add' := by
        intro v w
        funext j
        exact congrFun (map_add (g' (β j)) (fun i => v i.1) (fun i => w i.1)) _
      map_smul' := by
        intro c v
        funext j
        exact congrFun (map_smul (g' (β j)) c (fun i => v i.1)) _
      left_inv := by
        intro v
        funext j
        have e := blk_glue (β := β) (fun x => g' x (fun i' => v i'.1)) (β j)
        show (g' (β j)).symm (fun i : {k // β k = β j} => g' (β i.1) (fun i' => v i'.1) ⟨i.1, rfl⟩) ⟨j, rfl⟩ = v j
        rw [e, LinearEquiv.symm_apply_apply]
      right_inv := by
        intro v
        funext j
        have e := blk_glue (β := β) (fun x => (g' x).symm (fun i' => v i'.1)) (β j)
        show (g' (β j)) (fun i : {k // β k = β j} => (g' (β i.1)).symm (fun i' => v i'.1) ⟨i.1, rfl⟩) ⟨j, rfl⟩ = v j
        rw [e, LinearEquiv.apply_symm_apply] }
  let S : (J → F) ≃ₗ[L] (J → F) := LinearEquiv.piCongrRight fun j => (s j).toLinearEquiv
  refine ⟨S.trans ((G.restrictScalars L).trans S.symm), ?_⟩
  intro w j
  simp [S, G]

private theorem act_forall (σ : F ≃ₐ[L] F) (p : HeightOneSpectrum (𝓞 F) → Prop) :
    (∀ P, p (actP σ P)) ↔ ∀ P, p P := by
  constructor
  · intro h P
    obtain ⟨Q, rfl⟩ := (HeightOneSpectrum.equivOfRingEquiv
      (RingOfIntegers.mapRingEquiv σ.toRingEquiv)).surjective P
    exact h Q
  · intro h P
    exact h _

private theorem loc_iff (σ : F ≃ₐ[L] F) (b : 𝓞 L) (a : F) :
    (∀ P : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 L) (𝓞 F) b ∉ P.asIdeal → P.valuation F (σ a) ≤ 1) ↔
      ∀ P : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 L) (𝓞 F) b ∉ P.asIdeal → P.valuation F a ≤ 1 := by
  obtain ⟨hv, -, -, hm, -⟩ := cAct L F
  refine Iff.trans (act_forall σ (fun P => algebraMap (𝓞 L) (𝓞 F) b ∉ P.asIdeal →
    P.valuation F (σ a) ≤ 1)).symm ?_
  simp only [hm, hv]

private theorem lat_iff (σ : F ≃ₐ[L] F) (𝔟 𝔠 : HeightOneSpectrum (𝓞 F) →₀ ℤ) (h : ∀ P, 𝔠 (actP σ P) = 𝔟 P) (a : F) :
    (∀ P : HeightOneSpectrum (𝓞 F), P.valuation F (σ a) ≤ WithZero.exp (-𝔠 P)) ↔
      ∀ P : HeightOneSpectrum (𝓞 F), P.valuation F a ≤ WithZero.exp (-𝔟 P) := by
  obtain ⟨hv, -⟩ := cAct L F
  refine Iff.trans (act_forall σ (fun P => P.valuation F (σ a) ≤ WithZero.exp (-𝔠 P))).symm ?_
  simp only [hv, h]

end

theorem UpperTheory.V.ZK.Cl.cBlock :
    UpperTheory.V.ZK.Cl.CBlock := by
  intro L F _ _ _ _ _ J X s β g'
  refine ⟨blk_exists s β g', fun g hg => ⟨?_, ?_, ?_⟩⟩
  · have hg' : ∀ (w : J → F) (j : J), s j (g w j) = g' (β j) (fun i => s i.1 (w i.1)) ⟨j, rfl⟩ := hg
    intro u u' hu
    have hu' : ∀ k, s k (u k : F) = (u' (β k) : F) := fun k => by
      have := congrArg Units.val (hu k)
      simpa [UpperTheory.V.ZK.actU] using this
    show g * diag L u = diag L u * g
    refine LinearEquiv.ext fun w => funext fun j => ?_
    show g (diag L u w) j = diag L u (g w) j
    have hw : diag L u w = fun k => (u k : F) * w k := funext (diag_apply u w)
    rw [hw, diag_apply]
    apply (s j).injective
    rw [hg', map_mul, hg', hu']
    have e : (fun i : {k // β k = β j} => s i.1 ((u i.1 : F) * w i.1)) =
        (u' (β j) : F) • (fun i => s i.1 (w i.1)) := by
      funext i
      obtain ⟨k, hk⟩ := i
      simp only [map_mul, hu', Pi.smul_apply, smul_eq_mul, hk]
    rw [e, map_smul, Pi.smul_apply, smul_eq_mul]
  · classical
    have hg' : ∀ (w : J → F) (j : J), s j (g w j) = g' (β j) (fun i => s i.1 (w i.1)) ⟨j, rfl⟩ := hg
    intro b hb x w
    have hb' : ∀ W : J → F, InLoc b W ↔ InLoc b (g W) := hb
    let W : J → F := fun j => if h : β j = x then (s j).symm (w ⟨j, h⟩) else 0
    have hW : (fun i : {k // β k = x} => s i.1 (W i.1)) = w := by
      funext i
      obtain ⟨k, hk⟩ := i
      subst hk
      simp [W]
    have hW0 : ∀ j, β j ≠ x → W j = 0 := by
      intro j hj
      simp [W, hj]
    have h0 : ∀ j, β j ≠ x → g W j = 0 := by
      intro j hj
      apply (s j).injective
      rw [hg', map_zero]
      have hz : (fun i : {k // β k = β j} => s i.1 (W i.1)) = 0 := by
        funext i
        obtain ⟨k, hk⟩ := i
        have hk' : β k ≠ x := hk ▸ hj
        simp [hW0 k hk']
      rw [hz, map_zero]
      rfl
    have key : ∀ V : J → F, (∀ j, β j ≠ x → V j = 0) →
        (InLoc b V ↔ InLoc b (fun i : {k // β k = x} => s i.1 (V i.1))) := by
      intro V hV
      constructor
      · intro h i P hP
        exact (loc_iff (s i.1) b (V i.1)).2 (h i.1) P hP
      · intro h j P hP
        by_cases hj : β j = x
        · exact (loc_iff (s j) b (V j)).1 (h ⟨j, hj⟩) P hP
        · rw [hV j hj, map_zero]
          exact zero_le'
    have hgW : (fun i : {k // β k = x} => s i.1 (g W i.1)) = g' x w := by
      funext i
      rw [blk_apply hg W x i, hW]
    have := (key W hW0).symm.trans ((hb' W).trans (key (g W) h0))
    rw [hW, hgW] at this
    exact this
  · have hg' : ∀ (w : J → F) (j : J), s j (g w j) = g' (β j) (fun i => s i.1 (w i.1)) ⟨j, rfl⟩ := hg
    intro 𝔟 𝔠 h𝔠 hblk w
    constructor
    · intro hw j P
      apply (lat_iff (s j) (𝔟 j) (𝔠 j) (h𝔠 j) (g w j)).1 ?_ P
      intro Q
      rw [hg']
      have h2 : InLat 0 (fun i : {k // β k = β j} => s i.1 (w i.1)) := by
        intro i Q'
        exact (lat_iff (s i.1) 0 0 (fun _ => rfl) (w i.1)).2 (hw i.1) Q'
      exact (hblk (β j) _).1 h2 ⟨j, rfl⟩ Q
    · intro hw j P
      apply (lat_iff (s j) 0 0 (fun _ => rfl) (w j)).1 ?_ P
      intro Q
      have h2 : InLat (fun i : {k // β k = β j} => 𝔠 i.1) (g' (β j) (fun i => s i.1 (w i.1))) := by
        intro i Q'
        rw [← blk_apply hg w (β j) i]
        exact (lat_iff (s i.1) (𝔟 i.1) (𝔠 i.1) (h𝔠 i.1) (g w i.1)).2 (hw i.1) Q'
      exact (hblk (β j) _).2 h2 ⟨j, rfl⟩ Q
