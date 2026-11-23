import Formalism.SharpRestriction.GrowthBounds.RootWeights.EnvelopingMonoidPreservesStable

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def restrictOperators (E : GLOps n K V) (W : Submodule K V) (hW : ∀ a b, ∀ z ∈ W, E a b z ∈ W) : GLOps n K W :=
  fun a b => (E a b).restrict (hW a b)

def IsRestrictionOfAlt (W : Submodule K V) (u : Module.End K W) (u' : Module.End K V) : Prop :=
  ∀ z : W, (u z : V) = u' z

theorem restriction_compat_operator (E : GLOps n K V) (W : Submodule K V) (hW : ∀ a b, ∀ z ∈ W, E a b z ∈ W) (a b : Fin n) :
    IsRestrictionOfAlt W (restrictOperators E W hW a b) (E a b) := fun _ => rfl

theorem restriction_compat_one (W : Submodule K V) : IsRestrictionOfAlt W 1 1 := fun _ => rfl

theorem restriction_compat_mul {W : Submodule K V} {u v : Module.End K W} {u' v' : Module.End K V}
    (h1 : IsRestrictionOfAlt W u u') (h2 : IsRestrictionOfAlt W v v') : IsRestrictionOfAlt W (u * v) (u' * v') := fun z => by
  rw [Module.End.mul_apply, Module.End.mul_apply, h1, h2]

theorem restriction_compat_smul {W : Submodule K V} {u : Module.End K W} {u' : Module.End K V} (c : K)
    (h1 : IsRestrictionOfAlt W u u') : IsRestrictionOfAlt W (c • u) (c • u') := fun z => by
  rw [LinearMap.smul_apply, LinearMap.smul_apply, Submodule.coe_smul, h1]

theorem restriction_compat_sub {W : Submodule K V} {u v : Module.End K W} {u' v' : Module.End K V}
    (h1 : IsRestrictionOfAlt W u u') (h2 : IsRestrictionOfAlt W v v') : IsRestrictionOfAlt W (u - v) (u' - v') := fun z => by
  rw [LinearMap.sub_apply, LinearMap.sub_apply, Submodule.coe_sub, h1, h2]

theorem restriction_compat_pow {W : Submodule K V} {u : Module.End K W} {u' : Module.End K V}
    (h1 : IsRestrictionOfAlt W u u') (k : ℕ) : IsRestrictionOfAlt W (u ^ k) (u' ^ k) := by
  induction k with
  | zero => simpa using restriction_compat_one W
  | succ k ih => rw [pow_succ, pow_succ]; exact restriction_compat_mul ih h1

theorem restriction_compat_list_prod {W : Submodule K V} (l : List ℕ) (f : ℕ → Module.End K W) (f' : ℕ → Module.End K V)
    (h : ∀ j, IsRestrictionOfAlt W (f j) (f' j)) : IsRestrictionOfAlt W (l.map f).prod (l.map f').prod := by
  induction l with
  | nil => simpa using restriction_compat_one W
  | cons a l ih => rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons]; exact restriction_compat_mul (h a) ih

theorem integral_enveloping_lifts (E : GLOps n K V) (W : Submodule K V) (hW : ∀ a b, ∀ z ∈ W, E a b z ∈ W)
    (u : Module.End K W) (hu : u ∈ UZmon (restrictOperators E W hW)) : ∃ u' ∈ UZmon E, IsRestrictionOfAlt W u u' := by
  induction hu using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
    · exact ⟨divPowE E a b k, Submonoid.subset_closure (Or.inl ⟨a, b, k, hab, rfl⟩),
        restriction_compat_smul _ (restriction_compat_pow (restriction_compat_operator E W hW a b) k)⟩
    · exact ⟨binomE E a k, Submonoid.subset_closure (Or.inr ⟨a, k, rfl⟩),
        restriction_compat_smul _ (restriction_compat_list_prod _ _ _ fun j =>
          restriction_compat_sub (restriction_compat_operator E W hW a a) (restriction_compat_smul _ (restriction_compat_one W)))⟩
  | one => exact ⟨1, Submonoid.one_mem _, restriction_compat_one W⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', hx', hxc⟩ := hx
    obtain ⟨y', hy', hyc⟩ := hy
    exact ⟨x' * y', Submonoid.mul_mem _ hx' hy', restriction_compat_mul hxc hyc⟩

theorem enveloping_monoid_restricts (E : GLOps n K V) (W : Submodule K V) (hW : ∀ a b, ∀ z ∈ W, E a b z ∈ W)
    (u' : Module.End K V) (hu : u' ∈ Umon E) : ∃ u ∈ Umon (restrictOperators E W hW), IsRestrictionOfAlt W u u' := by
  induction hu using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨ab, rfl⟩ := hx
    exact ⟨restrictOperators E W hW ab.1 ab.2, Submonoid.subset_closure ⟨ab, rfl⟩, restriction_compat_operator E W hW ab.1 ab.2⟩
  | one => exact ⟨1, Submonoid.one_mem _, restriction_compat_one W⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', hx', hxc⟩ := hx
    obtain ⟨y', hy', hyc⟩ := hy
    exact ⟨x' * y', Submonoid.mul_mem _ hx' hy', restriction_compat_mul hxc hyc⟩

theorem restricted_weightSpace_iff (E : GLOps n K V) (W : Submodule K V) (hW : ∀ a b, ∀ z ∈ W, E a b z ∈ W)
    (mu : Fin n → ℤ) (z : W) : z ∈ weightSp (restrictOperators E W hW) mu ↔ (z : V) ∈ weightSp E mu := by
  rw [mem_weightSpace_iff_diag_action, mem_weightSpace_iff_diag_action]
  refine forall_congr' fun a => ?_
  rw [Subtype.ext_iff, Submodule.coe_smul]
  rfl

theorem restricted_operators_gl_relation {E : GLOps n K V}
    (hrel : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0))
    (W : Submodule K V) (hW : ∀ a b, ∀ z ∈ W, E a b z ∈ W) (a b c d : Fin n) :
    restrictOperators E W hW a b * restrictOperators E W hW c d - restrictOperators E W hW c d * restrictOperators E W hW a b =
      (if b = c then restrictOperators E W hW a d else 0) - (if d = a then restrictOperators E W hW c b else 0) := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  have h := LinearMap.congr_fun (hrel a b c d) (z : V)
  have hl : (((restrictOperators E W hW a b * restrictOperators E W hW c d - restrictOperators E W hW c d * restrictOperators E W hW a b) z : W) : V)
      = (E a b * E c d - E c d * E a b) (z : V) :=
    restriction_compat_sub (restriction_compat_mul (restriction_compat_operator E W hW a b) (restriction_compat_operator E W hW c d))
      (restriction_compat_mul (restriction_compat_operator E W hW c d) (restriction_compat_operator E W hW a b)) z
  rw [hl, h]
  have h0 : IsRestrictionOfAlt W 0 0 := fun _ => rfl
  refine (restriction_compat_sub (u := if b = c then restrictOperators E W hW a d else 0)
    (v := if d = a then restrictOperators E W hW c b else 0) ?_ ?_ z).symm
  · split_ifs
    · exact restriction_compat_operator E W hW a d
    · exact h0
  · split_ifs
    · exact restriction_compat_operator E W hW c b
    · exact h0

theorem generated_subrep_stable (E : GLOps n K V) (h : V) (a b : Fin n) (z : V) (hz : z ∈ generatedSubrep E h) :
    E a b z ∈ generatedSubrep E h := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    exact Submodule.subset_span ⟨E a b * u, Submonoid.mul_mem _ (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem mem_generated_subrep_self (E : GLOps n K V) (h : V) : h ∈ generatedSubrep E h :=
  Submodule.subset_span ⟨1, Submonoid.one_mem _, rfl⟩

theorem enveloping_word_maps_weight {E : GLOps n K V}
    (hrel : ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0))
    (u : Module.End K V) (hu : u ∈ Umon E) : ∀ (mu : Fin n → ℤ) (x : V), x ∈ weightSp E mu →
      ∃ mu', u x ∈ weightSp E mu' := by
  induction hu using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨ab, rfl⟩ := hx
    intro mu z hz
    exact ⟨_, operator_shifts_weight_by_root hrel ab.1 ab.2 mu z hz⟩
  | one => intro mu z hz; exact ⟨mu, by simpa using hz⟩
  | mul x y _ _ hx hy =>
    intro mu z hz
    obtain ⟨mu1, h1⟩ := hy mu z hz
    obtain ⟨mu2, h2⟩ := hx mu1 _ h1
    exact ⟨mu2, by rw [Module.End.mul_apply]; exact h2⟩

theorem restricted_generated_by_hwv (E : GLOps n K V) (h : V) :
    Submodule.span K {x : generatedSubrep E h | ∃ u ∈ Umon (restrictOperators E (generatedSubrep E h) (generated_subrep_stable E h)),
      x = u ⟨h, mem_generated_subrep_self E h⟩} = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨z, hz⟩ _
  have key : ∀ (x : V) (hx : x ∈ generatedSubrep E h), (⟨x, hx⟩ : generatedSubrep E h) ∈
      Submodule.span K {x : generatedSubrep E h | ∃ u ∈ Umon (restrictOperators E (generatedSubrep E h) (generated_subrep_stable E h)),
        x = u ⟨h, mem_generated_subrep_self E h⟩} := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u', hu', rfl⟩ := hx
      obtain ⟨u, hu, hc⟩ := enveloping_monoid_restricts E _ (generated_subrep_stable E h) u' hu'
      exact Submodule.subset_span ⟨u, hu, Subtype.ext (hc ⟨h, mem_generated_subrep_self E h⟩).symm⟩
    | zero => exact Submodule.zero_mem _
    | add x y hx hy ihx ihy => exact Submodule.add_mem _ ihx ihy
    | smul c x hx ihx => exact Submodule.smul_mem _ c ihx
  exact key z hz

theorem generated_restriction_irreducible [FiniteDimensional K V] {E : GLOps n K V} (hE : IsGLRep E) (lam : Fin n → ℤ)
    (hlam : Dominant lam) (h : V) (hh : h ∈ highestWeightVectors E lam) (h0 : h ≠ 0) :
    IsIrrHW (restrictOperators E (generatedSubrep E h) (generated_subrep_stable E h)) lam ⟨h, mem_generated_subrep_self E h⟩ := by
  have hh' := (mem_highestWeight_iff E lam h).1 hh
  have hrel := restricted_operators_gl_relation hE.1 (generatedSubrep E h) (generated_subrep_stable E h)
  have hw : (⟨h, mem_generated_subrep_self E h⟩ : generatedSubrep E h) ∈
      weightSp (restrictOperators E (generatedSubrep E h) (generated_subrep_stable E h)) lam :=
    (restricted_weightSpace_iff E _ _ lam _).2 hh'.1
  refine ⟨⟨hrel, fun x => ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩, ?_⟩, hlam,
    ⟨fun hc => h0 (congrArg Subtype.val hc), hw, fun a b hab => Subtype.ext (hh'.2 a b hab)⟩,
    restricted_generated_by_hwv E h⟩
  rw [eq_top_iff, ← restricted_generated_by_hwv E h]
  refine Submodule.span_le.2 ?_
  rintro x ⟨u, hu, rfl⟩
  obtain ⟨mu', hmu'⟩ := enveloping_word_maps_weight hrel u hu lam _ hw
  exact Submodule.mem_iSup_of_mem mu' hmu'

end

theorem integral_enveloping_preserves_lattice {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {n : ℕ}
    {V : Type} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
    (E : GLOps n (KK O) V) (M : Submodule O V) (hM : UZStable (O := O) E M)
    (u : Module.End (KK O) V) (hu : u ∈ UZmon E) : ∀ x ∈ M, u x ∈ M := by
  induction hu using Submonoid.closure_induction with
  | mem x hx => exact hM x hx
  | one => intro z hz; simpa using hz
  | mul x y _ _ hx hy => intro z hz; rw [Module.End.mul_apply]; exact hx _ (hy z hz)

theorem generated_lattice_corollary_of_thm (D : Formalism.BasicNotions.D7) (h12 : NablaDeltaComparisonField D) (hB : GeneratedMultipleOfHWV) : GeneratedLatticeCorollary := by
  intro p n' O _ _ _ S hG n _ V _ _ _ _ _ E hE M hM lam hlam π hπ h hhM hhHW hh0 c y hy hyp
  have hIrr := generated_restriction_irreducible hE lam hlam h hhHW hh0
  have hT := (h12 p n' O S hG n lam (generatedSubrep E h) (restrictOperators E (generatedSubrep E h) (generated_subrep_stable E h))
    ⟨h, mem_generated_subrep_self E h⟩ hIrr).1
  have hp0 : (p : KK O) ≠ 0 := by
    intro h0
    apply S.p_ne
    apply IsFractionRing.injective O (KK O)
    rw [map_natCast, map_zero]; exact h0
  have hpc : (p : KK O) ^ c ≠ 0 := zpow_ne_zero _ hp0
  have hx : (((p : KK O) ^ c)⁻¹ • (⟨y, hy⟩ : generatedSubrep E h)) ∈
      Nabla (O := O) (restrictOperators E (generatedSubrep E h) (generated_subrep_stable E h)) lam ⟨h, mem_generated_subrep_self E h⟩ := by
    intro u hu
    obtain ⟨u', hu', hc⟩ := integral_enveloping_lifts E _ _ u hu
    obtain ⟨o, ho⟩ := hyp u' hu'
    refine ⟨o, ?_⟩
    have hmem : u' y ∈ generatedSubrep E h := by
      have := (u ⟨y, hy⟩).2
      rwa [hc ⟨y, hy⟩] at this
    obtain ⟨a', ha', r, hr, hsum⟩ := Submodule.mem_sup.1 (hB (KK O) V n E hE lam h hhHW hmem)
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 ha'
    have hker : (⨆ mu ∈ {mu : Fin n → ℤ | mu ≠ lam}, (weightSp E mu ⊓ generatedSubrep E h)) ≤ LinearMap.ker π :=
      iSup₂_le fun mu hmu z hz => LinearMap.mem_ker.2 (hπ.2 mu hmu z hz.1)
    have hπr : π r = 0 := LinearMap.mem_ker.1 (hker hr)
    have hπh : π h = h := hπ.1 h ((mem_highestWeight_iff E lam h).1 hhHW).1
    have hπu : π (u' y) = a • h := by rw [← hsum, map_add, map_smul, hπh, hπr, add_zero]
    have hr' : r = u' y - ((p : KK O) ^ c * algebraMap O (KK O) o) • h := by
      rw [← ho, hπu, ← hsum]; abel
    have hle : (⨆ mu ∈ {mu : Fin n → ℤ | mu ≠ lam}, (weightSp E mu ⊓ generatedSubrep E h)) ≤
        (otherWts (restrictOperators E (generatedSubrep E h) (generated_subrep_stable E h)) lam).map (generatedSubrep E h).subtype :=
      iSup₂_le fun mu hmu z hz => ⟨⟨z, hz.2⟩,
        Submodule.mem_iSup_of_mem mu (Submodule.mem_iSup_of_mem hmu ((restricted_weightSpace_iff E _ _ mu _).2 hz.1)), rfl⟩
    obtain ⟨w, hw, hwr⟩ := hle hr
    have hwr' : (w : V) = r := hwr
    have hfin : u (((p : KK O) ^ c)⁻¹ • (⟨y, hy⟩ : generatedSubrep E h)) -
        (algebraMap O (KK O) o) • (⟨h, mem_generated_subrep_self E h⟩ : generatedSubrep E h) = ((p : KK O) ^ c)⁻¹ • w := by
      apply Subtype.ext
      rw [map_smul, Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_smul, hc, hwr', hr',
        smul_sub, smul_smul, ← mul_assoc, inv_mul_cancel₀ hpc, one_mul]
    rw [hfin]
    exact Submodule.smul_mem _ _ hw
  have hDel := hT _ hx
  have hDM : ∀ w ∈ Delta (O := O) (restrictOperators E (generatedSubrep E h) (generated_subrep_stable E h))
      (⟨h, mem_generated_subrep_self E h⟩ : generatedSubrep E h), (w : V) ∈ M := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨u, hu, rfl⟩ := hz
      obtain ⟨u', hu', hc⟩ := integral_enveloping_lifts E _ _ u hu
      rw [hc]
      exact integral_enveloping_preserves_lattice E M hM.1 u' hu' h hhM
    | zero => exact M.zero_mem
    | add z1 z2 _ _ h1 h2 => rw [Submodule.coe_add]; exact M.add_mem h1 h2
    | smul o z _ hz => rw [Submodule.coe_smul_of_tower]; exact M.smul_mem o hz
  refine ⟨_, hDM _ hDel, ?_⟩
  have hcoef : (p : KK O) ^ (c - ((N0 n * deF p n (ellWt lam) : ℕ) : ℤ)) *
      ((p : KK O) ^ (N0 n * deF p n (ellWt lam)) * ((p : KK O) ^ c)⁻¹) = 1 := by
    rw [zpow_sub₀ hp0, zpow_natCast]
    field_simp
  rw [Submodule.coe_smul_of_tower, Submodule.coe_smul, ← algebraMap_smul (KK O) ((p : O) ^ (N0 n * deF p n (ellWt lam))),
    smul_smul, smul_smul, map_pow, map_natCast, mul_assoc, hcoef, one_smul]

end Formalism.MainNotions.G.GLWeightTheory
