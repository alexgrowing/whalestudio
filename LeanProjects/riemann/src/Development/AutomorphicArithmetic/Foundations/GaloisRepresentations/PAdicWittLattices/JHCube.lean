import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.CechCubeBaseChange.BcSumSingle
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.OmegaPullSCompRight
import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.Leaves

open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

section
variable {k k' : Type} [CommRing k] [CommRing k'] [Algebra k k'] {J : Type}
  (e : Module.Basis J k k')

private theorem bcSum_mapRange {M N M' N' : Type} [AddCommGroup M] [Module k M] [AddCommGroup N]
    [Module k' N] [AddCommGroup M'] [Module k M'] [AddCommGroup N'] [Module k' N']
    (ψ : M →ₛₗ[algebraMap k k'] N) (ψ' : M' →ₛₗ[algebraMap k k'] N') (f : M → M') (hf : f 0 = 0)
    (hfa : ∀ a b, f (a + b) = f a + f b) (g : N →ₗ[k'] N') (h : ∀ m, ψ' (f m) = g (ψ m))
    (x : J →₀ M) : bcSum e ψ' (x.mapRange f hf) = g (bcSum e ψ x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [Finsupp.mapRange_add hfa, map_add, map_add, map_add, ha, hb]
  | single j m => rw [Finsupp.mapRange_single, bcSum_single, bcSum_single, map_smul, h]

private theorem isBC_pi {T : Type} [Finite T] {M N : T → Type} [∀ t, AddCommGroup (M t)]
    [∀ t, Module k (M t)] [∀ t, AddCommGroup (N t)] [∀ t, Module k' (N t)]
    (ψ : ∀ t, M t →ₛₗ[algebraMap k k'] N t)
    (Ψ : (∀ t, M t) →ₛₗ[algebraMap k k'] (∀ t, N t)) (hΨ : ∀ x t, Ψ x t = ψ t (x t))
    (h : ∀ t, IsBC e (ψ t)) : IsBC e Ψ := by
  classical
  have := Fintype.ofFinite T
  have key : ∀ (x : J →₀ ∀ t, M t) t,
      bcSum e Ψ x t = bcSum e (ψ t) (x.mapRange (fun m => m t) rfl) := by
    intro x t
    have := bcSum_mapRange e Ψ (ψ t) (fun m => m t) rfl (fun a b => rfl) (LinearMap.proj t)
      (fun m => (hΨ m t).symm) x
    simpa using this.symm
  constructor
  · intro x y hxy
    ext j t
    have h1 : x.mapRange (fun m => m t) rfl = y.mapRange (fun m => m t) rfl := by
      apply (h t).1
      rw [← key, ← key, hxy]
    have := congrArg (fun z => z j) h1
    simpa using this
  · intro y
    choose x hx using fun t => (h t).2 (y t)
    refine ⟨∑ t, (x t).mapRange (Pi.single t) (Pi.single_zero t), ?_⟩
    rw [map_sum]
    have hs : ∀ t, bcSum e Ψ ((x t).mapRange (Pi.single t) (Pi.single_zero t)) = Pi.single t (y t) := by
      intro t
      rw [bcSum_mapRange e (ψ t) Ψ (Pi.single t) (Pi.single_zero t)
        (fun a b => Pi.single_add t a b) (LinearMap.single k' N t) ?_ (x t)]
      · simp [hx]
      · intro m
        funext s
        rw [hΨ]
        by_cases hst : s = t
        · subst hst
          simp
        · simp [Pi.single_eq_of_ne hst]
    simp only [hs]
    exact Finset.univ_sum_single y

end

theorem UpperTheory.Gal.G3.jHCube :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_cube := by
  unfold P_cube
  intro k k' _ _ _ J e ι _ _ A B ψ hψ
  classical
  have := Fintype.ofFinite ι
  have hT : ∀ q, IsBC e (ψ.term (q + 1)) := by
    intro q
    exact isBC_pi e (fun s : {s : Finset ι // s.card = q + 1} => ψ.app s.1) (ψ.term (q + 1))
      (fun x s => rfl) (fun s => hψ s.1 (Finset.card_pos.1 (by rw [s.2]; omega)))
  have hd : ∀ q (w : J →₀ A.Term q), bcSum e (ψ.term (q + 1)) (w.mapRange (A.d q) (map_zero _))
      = B.d q (bcSum e (ψ.term q) w) := fun q w =>
    bcSum_mapRange e (ψ.term q) (ψ.term (q + 1)) (A.d q) (map_zero _) (fun a b => map_add _ a b)
      (B.d q) (fun m => ψ.term_d q m) w
  have hz : ∀ q (x : J →₀ (A.d q).ker), ((bcSum e (ψ.cocycle q) x : (B.d q).ker) : B.Term q)
      = bcSum e (ψ.term q) (x.mapRange Subtype.val rfl) := fun q x =>
    (bcSum_mapRange e (ψ.cocycle q) (ψ.term q) Subtype.val rfl (fun a b => rfl)
      (B.d q).ker.subtype (fun m => rfl) x).symm
  have hZ : ∀ q, IsBC e (ψ.cocycle (q + 1)) := by
    intro q
    constructor
    · intro x y hxy
      have h1 := congrArg Subtype.val hxy
      rw [hz, hz] at h1
      have h2 := (hT q).1 h1
      refine Finsupp.ext fun j => Subtype.ext ?_
      simpa using congrArg (fun w => w j) h2
    · intro z
      obtain ⟨w, hw⟩ := (hT q).2 (z : B.Term (q + 1))
      have h0 : w.mapRange (A.d (q + 1)) (map_zero _) = 0 := by
        apply (hT (q + 1)).1
        rw [hd, hw, map_zero]
        exact (LinearMap.mem_ker).1 z.2
      have hw0 : ∀ j, A.d (q + 1) (w j) = 0 := fun j => by
        simpa using congrArg (fun v => v j) h0
      let x : J →₀ (A.d (q + 1)).ker :=
        w.mapRange (fun v => if hv : A.d (q + 1) v = 0 then (⟨v, hv⟩ : (A.d (q + 1)).ker) else 0)
          (by simp; rfl)
      have hxw : x.mapRange Subtype.val rfl = w := by
        ext j
        simp [x, hw0 j]
      refine ⟨x, Subtype.ext ?_⟩
      rw [hz, hxw, hw]
  intro p
  have hH : ∀ x : J →₀ (A.d (p + 1)).ker,
      bcSum e (ψ.homology p) (x.mapRange (cechClass A p) (map_zero _))
        = cechClass B p (bcSum e (ψ.cocycle (p + 1)) x) := fun x =>
    bcSum_mapRange e (ψ.cocycle (p + 1)) (ψ.homology p) (cechClass A p) (map_zero _)
      (fun a b => map_add _ a b) (cechClass B p) (fun m => ψ.homology_cechClass p m) x
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨x, rfl⟩ := Finsupp.mapRange_surjective _ (map_zero (cechClass A p))
      (cechClass_surjective A p) c
    rw [hH] at hc
    cases p with
    | zero =>
      rw [cechClass_zero_eq_zero_iff] at hc
      have hx : x = 0 := (hZ 0).1 (by rw [hc, map_zero])
      simp [hx]
    | succ q =>
      rw [cechClass_succ_eq_zero_iff] at hc
      obtain ⟨y, hy⟩ := hc
      obtain ⟨w, rfl⟩ := (hT q).2 y
      rw [← hd, hz] at hy
      have h2 := (hT (q + 1)).1 hy
      ext j
      have hj := congrArg (fun v => v j) h2
      simp only [Finsupp.mapRange_apply] at hj
      simp only [Finsupp.mapRange_apply, Finsupp.coe_zero, Pi.zero_apply]
      rw [cechClass_succ_eq_zero_iff]
      exact ⟨w j, hj⟩
  · intro h
    obtain ⟨z, rfl⟩ := cechClass_surjective B p h
    obtain ⟨x, rfl⟩ := (hZ p).2 z
    exact ⟨_, hH x⟩
