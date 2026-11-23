import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps
import Development.EtaleCohomology.CyclotomicDiscriminants.SZcTPf
import Development.EtaleCohomology.CyclotomicDiscriminants.SChainPf

noncomputable section
namespace LateralTheory.Q.SRelT
open UpperTheory.V.ZK

def Gen (M : Type) [AddCommGroup M] (r : ℕ) : Prop :=
  ∃ (F : Type) (_ : AddCommGroup F), Module.Free ℤ F ∧ Module.Finite ℤ F ∧ Module.finrank ℤ F ≤ r ∧
    ∃ f : F →+ M, Function.Surjective f

theorem Gen.surj {M N : Type} [AddCommGroup M] [AddCommGroup N] {r : ℕ} (h : Gen M r) (g : M →+ N)
    (hg : Function.Surjective g) : Gen N r := by
  obtain ⟨F, _, h1, h2, h3, f, hf⟩ := h
  exact ⟨F, inferInstance, h1, h2, h3, g.comp f, hg.comp hf⟩

theorem Gen.mono {M : Type} [AddCommGroup M] {r s : ℕ} (h : Gen M r) (hs : r ≤ s) : Gen M s := by
  obtain ⟨F, _, h1, h2, h3, f, hf⟩ := h
  exact ⟨F, inferInstance, h1, h2, h3.trans hs, f, hf⟩

theorem gen_zero {M : Type} [AddCommGroup M] [Subsingleton M] : Gen M 0 :=
  ⟨PUnit, inferInstance, inferInstance, inferInstance, (Module.finrank_zero_of_subsingleton).le, 0, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

theorem gen_zmod (q : ℕ) : Gen (ZMod q) 1 :=
  ⟨ℤ, inferInstance, inferInstance, inferInstance, by simp, Int.castAddHom _, ZMod.intCast_surjective⟩

theorem Gen.ext {M1 M2 M3 : Type} [AddCommGroup M1] [AddCommGroup M2] [AddCommGroup M3] {a b : ℕ}
    (f : M1 →+ M2) (g : M2 →+ M3) (hfg : ∀ x, g x = 0 → ∃ y, f y = x) (h1 : Gen M1 a) (h3 : Gen M3 b) :
    Gen M2 (a + b) := by
  obtain ⟨F, _, a1, a2, a3, φ, hφ⟩ := h1
  obtain ⟨E, _, b1, b2, b3, ψ, hψ⟩ := h3
  let g' := g.toIntLinearMap
  let E' : Submodule ℤ E := (LinearMap.range g').comap ψ.toIntLinearMap
  let u : E' →ₗ[ℤ] LinearMap.range g' :=
    LinearMap.codRestrict _ (ψ.toIntLinearMap ∘ₗ E'.subtype) fun x => x.2
  obtain ⟨w, hw⟩ := Module.projective_lifting_property g'.rangeRestrict u g'.surjective_rangeRestrict
  refine ⟨F × E', inferInstance, inferInstance, inferInstance, ?_, (f.comp φ).coprod w.toAddMonoidHom, ?_⟩
  · rw [Module.finrank_prod]
    have := Submodule.finrank_le E'
    omega
  · intro m
    obtain ⟨x, hx⟩ := hψ (g m)
    have hx' : x ∈ E' := ⟨m, hx.symm⟩
    have e : g (w ⟨x, hx'⟩) = ψ x := congrArg Subtype.val (LinearMap.congr_fun hw ⟨x, hx'⟩)
    obtain ⟨y, hy⟩ := hfg (m - w ⟨x, hx'⟩) (by rw [map_sub, e, hx, sub_self])
    obtain ⟨z, rfl⟩ := hφ y
    exact ⟨(z, ⟨x, hx'⟩), by simp [hy]⟩

theorem Gen.rel {M : Type} [AddCommGroup M] {r : ℕ} (h : Gen M r) (l : ℕ) (hl : 2 ≤ l) (x : Fin (r + 1) → M) :
    ∃ (n : Fin (r + 1) → ℤ) (t : Fin (r + 1)), ¬ (l : ℤ) ∣ n t ∧ ∑ i, n i • x i = 0 := by
  obtain ⟨F, _, h1, h2, h3, f, hf⟩ := h
  choose y hy using fun i => hf (x i)
  have hn : ¬ LinearIndependent ℤ y := fun hi => by
    have := hi.fintype_card_le_finrank
    simp at this
    omega
  rw [Fintype.not_linearIndependent_iff] at hn
  obtain ⟨n, hn, t, ht⟩ := hn
  have key : ∀ (s : ℕ) (n : Fin (r + 1) → ℤ), (n t).natAbs = s → n t ≠ 0 → ∑ i, n i • y i = 0 →
      ∃ (n : Fin (r + 1) → ℤ) (t : Fin (r + 1)), ¬ (l : ℤ) ∣ n t ∧ ∑ i, n i • y i = 0 := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro n hs h0 hn
      by_cases hd : ∀ i, (l : ℤ) ∣ n i
      · choose m hm using hd
        have hm0 : m t ≠ 0 := fun h => h0 (by rw [hm, h, mul_zero])
        refine ih (m t).natAbs ?_ m rfl hm0 ?_
        · rw [← hs, hm, Int.natAbs_mul, Int.natAbs_natCast]
          have := Int.natAbs_pos.2 hm0
          nlinarith
        · have : (l : ℤ) • ∑ i, m i • y i = 0 := by
            rw [Finset.smul_sum, ← hn]
            exact Finset.sum_congr rfl fun i _ => by rw [hm, mul_smul]
          exact (smul_eq_zero.1 this).resolve_left (by omega)
      · push Not at hd
        obtain ⟨i, hi⟩ := hd
        exact ⟨n, i, hi, hn⟩
  obtain ⟨m, t, h1, h2⟩ := key _ n rfl ht hn
  refine ⟨m, t, h1, ?_⟩
  have := congrArg f h2
  simpa [map_sum, hy] using this

theorem exists_prim {k : Type} [CommRing k] {q : ℕ} [NeZero q] (F : ZMod q → k) (hF : ∑ j, F j = 0) :
    ∃ E : ZMod q → k, ∀ j, E (j + 1) - E j = F j := by
  refine ⟨fun j => ∑ i ∈ Finset.range j.val, F i, fun j => ?_⟩
  have hq : ∑ i ∈ Finset.range q, F i = 0 := by
    rw [← hF, Finset.sum_range fun i => F i]
    obtain ⟨q, rfl⟩ : ∃ p, q = p + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne q)
    exact Finset.sum_congr rfl fun i _ => congrArg F (ZMod.natCast_zmod_val (n := q + 1) i)
  have hj : ∑ i ∈ Finset.range (j + 1).val, F i = ∑ i ∈ Finset.range (j.val + 1), F i := by
    have h1 : (j + 1).val = (j.val + 1) % q := by
      rw [← ZMod.val_natCast]; simp
    have h2 := ZMod.val_lt j
    rcases Nat.lt_or_ge (j.val + 1) q with h | h
    · rw [h1, Nat.mod_eq_of_lt h]
    · have : j.val + 1 = q := by omega
      rw [h1, this, hq]; simp
  simp only []
  rw [hj, Finset.sum_range_succ]; simp

open CategoryTheory Limits groupHomology

section Cat
variable {k G : Type} [CommRing k] [Group G]

theorem gen_exact (S : ShortComplex (ModuleCat k)) (h : S.Exact) {a b : ℕ} (h1 : Gen S.X₁ a) (h3 : Gen S.X₃ b) :
    Gen S.X₂ (a + b) :=
  Gen.ext S.f.hom.toAddMonoidHom S.g.hom.toAddMonoidHom ((ShortComplex.moduleCat_exact_iff S).1 h) h1 h3

theorem gen_epi {M N : ModuleCat k} (f : M ⟶ N) [Epi f] {a : ℕ} (h : Gen M a) : Gen N a :=
  h.surj f.hom.toAddMonoidHom ((ModuleCat.epi_iff_surjective f).1 inferInstance)

theorem gen_les (S : ShortComplex (Rep k G)) (h : S.ShortExact) (n : ℕ) {a b : ℕ}
    (h1 : Gen (groupHomology S.X₂ (n + 1)) a) (h3 : Gen (groupHomology S.X₁ n) b) :
    Gen (groupHomology S.X₃ (n + 1)) (a + b) :=
  gen_exact _ (mapShortComplex₃_exact h (i := n + 1) (j := n) rfl) h1 h3

theorem rep_exact (S : ShortComplex (Rep k G)) (h : ∀ x, S.g.hom x = 0 → ∃ y, S.f.hom y = x) : S.Exact := by
  apply (forget₂ _ (ModuleCat k)).reflects_exact_of_faithful
  rw [ShortComplex.moduleCat_exact_iff]
  exact h

theorem four (A W : Rep k G) (i : A ⟶ W) (T : W ⟶ W) (s : W ⟶ A) (w1 : i ≫ T = 0) (w2 : T ≫ s = 0)
    (hi : Function.Injective i.hom) (hs : Function.Surjective s.hom)
    (e1 : ∀ x, T.hom x = 0 → ∃ y, i.hom y = x) (e2 : ∀ x, s.hom x = 0 → ∃ y, T.hom y = x) :
    (∀ a b, Gen (groupHomology W 1) a → Gen (groupHomology W 0) b → Gen (groupHomology A 1) (a + b)) ∧
    ∀ n a b c, Gen (groupHomology W (n + 2)) a → Gen (groupHomology W (n + 1)) b → Gen (groupHomology A n) c →
      Gen (groupHomology A (n + 2)) (a + (b + c)) := by
  have : Epi s := (Rep.epi_iff_surjective s).2 hs
  have : Mono i := (Rep.mono_iff_injective i).2 hi
  have E2 : (ShortComplex.mk T s w2).Exact := rep_exact _ e2
  have : Epi (kernel.lift s T w2) := E2.epi_kernelLift
  have S1 : (ShortComplex.mk (kernel.ι s) s (kernel.condition s)).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel s) }
  have w3 : i ≫ kernel.lift s T w2 = 0 := by
    rw [← cancel_mono (kernel.ι s)]; simp [w1]
  have S2 : (ShortComplex.mk i (kernel.lift s T w2) w3).ShortExact :=
    { exact := rep_exact _ fun x hx => e1 x (by
        have hx' : (kernel.lift s T w2).hom x = 0 := hx
        rw [← kernel.lift_ι s T w2, Rep.hom_comp]
        simp [hx']) }
  refine ⟨fun a b h1 h2 => gen_les _ S1 0 h1 ?_, fun n a b c h1 h2 h3 => gen_les _ S1 (n + 1) h1 (gen_les _ S2 n h2 h3)⟩
  exact gen_epi (groupHomology.map (MonoidHom.id G) (kernel.lift s T w2) 0) h2

end Cat

section Perm
variable (k : Type) [CommRing k] {G : Type} [Group G] {q : ℕ} [NeZero q] (p : G →* Multiplicative (ZMod q))

def tr : Representation k G (ZMod q → k) where
  toFun g := LinearMap.funLeft k k fun j => j + Multiplicative.toAdd (p g)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [add_assoc]

theorem tr_apply (g : G) (F : ZMod q → k) (j : ZMod q) : tr k p g F j = F (j + Multiplicative.toAdd (p g)) := rfl

def trIso (hp : Function.Surjective p) : Rep.of (tr k p) ≅ Rep.coind p.ker.subtype (Rep.trivial k p.ker k) :=
  Rep.mkIso <| .mk (LinearEquiv.ofBijective
    (LinearMap.codRestrict (Representation.coindV p.ker.subtype (Representation.trivial k p.ker k))
      (LinearMap.funLeft k k fun h : G => Multiplicative.toAdd (p h)) fun F => (Representation.mem_coindV _ _ _).2 fun g h => by
      have : p g = 1 := g.2
      simp [this]) <| by
      constructor
      · intro F F' h
        funext j
        obtain ⟨g, hg⟩ := hp (Multiplicative.ofAdd j)
        have : F (Multiplicative.toAdd (p g)) = F' (Multiplicative.toAdd (p g)) := congrFun (congrArg Subtype.val h) g
        simpa [hg] using this
      · intro f
        choose σ hσ using hp
        refine ⟨fun j => f.1 (σ (Multiplicative.ofAdd j)), Subtype.ext (funext fun h => ?_)⟩
        have := f.2 ⟨σ (p h) * h⁻¹, by simp [MonoidHom.mem_ker, hσ]⟩ h
        show f.1 (σ (p h)) = f.1 h
        simpa using this)
    fun g => by
      refine LinearMap.ext fun F => Subtype.ext (funext fun h => ?_)
      show F (Multiplicative.toAdd (p h) + Multiplicative.toAdd (p g)) = F (Multiplicative.toAdd (p (h * g)))
      simp

theorem gen_tr [Finite G] (hp : Function.Surjective p) (n a : ℕ)
    (h : Gen (groupHomology (Rep.trivial k p.ker k) n) a) : Gen (groupHomology (Rep.of (tr k p)) n) a := by
  classical
  exact gen_epi ((indIso p.ker (Rep.trivial k p.ker k) n).symm ≪≫
    (functor k G n).mapIso (Rep.indCoindIso (Rep.trivial k p.ker k) ≪≫ (trIso k p hp).symm)).hom h

theorem step [Finite G] (hp : Function.Surjective p) :
    (∀ a b, Gen (groupHomology (Rep.trivial k p.ker k) 1) a → Gen (groupHomology (Rep.trivial k p.ker k) 0) b →
      Gen (groupHomology (Rep.trivial k G k) 1) (a + b)) ∧
    ∀ n a b c, Gen (groupHomology (Rep.trivial k p.ker k) (n + 2)) a →
      Gen (groupHomology (Rep.trivial k p.ker k) (n + 1)) b → Gen (groupHomology (Rep.trivial k G k) n) c →
      Gen (groupHomology (Rep.trivial k G k) (n + 2)) (a + (b + c)) := by
  let i : k →ₗ[k] (ZMod q → k) := LinearMap.pi fun _ => LinearMap.id
  let T : (ZMod q → k) →ₗ[k] (ZMod q → k) := LinearMap.funLeft k k (fun j => j + 1) - LinearMap.id
  let s : (ZMod q → k) →ₗ[k] k := ∑ j, LinearMap.proj j
  have hs : ∀ F, s F = ∑ j, F j := fun F => by simp [s]
  have hT : ∀ F j, T F j = F (j + 1) - F j := fun _ _ => rfl
  have hi : ∀ a j, i a j = a := fun _ _ => rfl
  have hsh : ∀ (F : ZMod q → k) (c : ZMod q), ∑ j, F (j + c) = ∑ j, F j := fun F c =>
    Equiv.sum_comp (Equiv.addRight c) F
  have := four (Rep.trivial k G k) (Rep.of (tr k p))
    (Rep.ofHom ⟨i, fun g => LinearMap.ext fun _ => rfl⟩)
    (Rep.ofHom ⟨T, fun g => LinearMap.ext fun F => funext fun j => by
      show T (tr k p g F) j = tr k p g (T F) j
      simp only [hT, tr_apply, add_right_comm]⟩)
    (Rep.ofHom ⟨s, fun g => LinearMap.ext fun F => by
      show s (tr k p g F) = s F
      simp only [hs, tr_apply, hsh]⟩)
    (by
      ext j
      show T (i 1) j = 0
      rw [hT, hi, hi, sub_self])
    (Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun F => by
      show s (T F) = 0
      simp only [hs, hT, Finset.sum_sub_distrib, hsh, sub_self])))
    (fun a b h => congrFun h 0)
    (fun a => ⟨Pi.single 0 a, by
      show s (Pi.single 0 a) = a
      simp [hs]⟩)
    (fun F hF => ⟨F 0, funext fun j => by
      have h1 : ∀ j, F (j + 1) = F j := fun j => sub_eq_zero.1 (congrFun hF j)
      have h2 : ∀ m : ℕ, F m = F 0 := fun m => by
        induction m with
        | zero => simp
        | succ m ih => rw [Nat.cast_succ, h1, ih]
      show F 0 = F j
      rw [← h2 j.val, ZMod.natCast_zmod_val]⟩)
    (fun F hF => by
      obtain ⟨E, hE⟩ := exists_prim F ((hs F).symm.trans hF)
      exact ⟨E, funext hE⟩)
  exact ⟨fun a b h1 h2 => this.1 a b (gen_tr k p hp _ _ h1) (gen_tr k p hp _ _ h2),
    fun n a b c h1 h2 h3 => this.2 n a b c (gen_tr k p hp _ _ h1) (gen_tr k p hp _ _ h2) h3⟩

end Perm

theorem groupHomology_zero_zmod_trivial_rep_generated_by_one (r : ℕ) (G : Type) [Group G] : Gen (groupHomology (Rep.trivial (ZMod r) G (ZMod r)) 0) 1 :=
  gen_epi (H0IsoOfIsTrivial (Rep.trivial (ZMod r) G (ZMod r))).inv (gen_zmod r)

theorem gen_triv (k G : Type) [CommRing k] [Group G] [Subsingleton G] (n : ℕ) :
    Gen (groupHomology (Rep.trivial k G k) (n + 1)) 0 := by
  have := ModuleCat.subsingleton_of_isZero (isZero_groupHomology_succ_of_subsingleton (Rep.trivial k G k) n)
  exact gen_zero

theorem gen_cyc (r : ℕ) {G : Type} [Group G] [Finite G] {q : ℕ} [NeZero q] (p : G →* Multiplicative (ZMod q))
    (hp : Function.Bijective p) (n : ℕ) : Gen (groupHomology (Rep.trivial (ZMod r) G (ZMod r)) n) 1 := by
  have : Subsingleton p.ker := by
    rw [(MonoidHom.ker_eq_bot_iff p).2 hp.1]; infer_instance
  have hs := step (ZMod r) p hp.2
  induction n using Nat.twoStepInduction with
  | zero => exact groupHomology_zero_zmod_trivial_rep_generated_by_one r G
  | one => exact hs.1 0 1 (gen_triv _ _ 0) (groupHomology_zero_zmod_trivial_rep_generated_by_one r _)
  | more n ih _ => exact hs.2 n 0 0 1 (gen_triv _ _ _) (gen_triv _ _ _) ih

theorem gen_two (r q : ℕ) [NeZero q] (e : ℕ) :
    Gen (groupHomology (Rep.trivial (ZMod r) (Cq q × Cq q) (ZMod r)) (2 * e)) (2 * e + 1) := by
  let p : Cq q × Cq q →* Cq q := MonoidHom.fst _ _
  have hp : Function.Surjective p := Prod.fst_surjective
  have hb : Function.Bijective ((MonoidHom.snd (Cq q) (Cq q)).comp p.ker.subtype) := by
    constructor
    · intro x y h
      exact Subtype.ext (Prod.ext (Eq.trans x.2 (Eq.symm y.2)) h)
    · intro c
      exact ⟨⟨(1, c), rfl⟩, rfl⟩
  induction e with
  | zero => exact groupHomology_zero_zmod_trivial_rep_generated_by_one r _
  | succ e ih =>
    exact ((step (ZMod r) p hp).2 (2 * e) 1 1 _ (gen_cyc r _ hb _) (gen_cyc r _ hb _) ih).mono (by omega)

theorem d_eq_bd (k G : Type) [CommRing k] [Group G] (m : ℕ) (z : Ch k G (m + 1)) :
    (inhomogeneousChains (Rep.trivial k G k)).d (m + 1) m z = bd k G m z := by
  rw [inhomogeneousChains.d_def]
  have : (inhomogeneousChains.d (Rep.trivial k G k) m).hom = bd k G m := by
    refine Finsupp.lhom_ext' fun g => LinearMap.ext_ring ?_
    have := inhomogeneousChains.d_single (A := Rep.trivial k G k) m g 1
    simpa [bd] using this
  exact LinearMap.congr_fun this z

theorem rel_bd (k G : Type) [CommRing k] [Group G] (m r l : ℕ) (hl : 2 ≤ l)
    (h : Gen (groupHomology (Rep.trivial k G k) (m + 1)) r) (z : Fin (r + 1) → Ch k G (m + 1)) (hz : ∀ t, Cyc (z t)) :
    ∃ (n : Fin (r + 1) → ℤ) (t : Fin (r + 1)), ¬ (l : ℤ) ∣ n t ∧ Bd (∑ i, (n i : k) • z i) := by
  let A := Rep.trivial k G k
  let c : Fin (r + 1) → cycles A (m + 1) := fun t =>
    cyclesMk (A := A) (m + 1) m (by simp) (z t) ((d_eq_bd k G m _).trans (hz t))
  have hc : ∀ t, iCycles A (m + 1) (c t) = z t := fun t => iCycles_mk _ _ _
  obtain ⟨n, t, h1, h2⟩ := h.rel l hl fun t => π A (m + 1) (c t)
  refine ⟨n, t, h1, ?_⟩
  have ex := ShortComplex.exact_of_g_is_cokernel
    (ShortComplex.mk _ _ ((inhomogeneousChains A).toCycles_comp_homologyπ (m + 2) (m + 1)))
    ((inhomogeneousChains A).homologyIsCokernel (m + 2) (m + 1) (by simp))
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 ex (∑ i, n i • c i) (by
    refine Eq.trans ?_ h2
    show (π A (m + 1)).hom (∑ i, n i • c i) = ∑ i, n i • (π A (m + 1)).hom (c i)
    simp only [map_sum, map_zsmul])
  refine ⟨y, ?_⟩
  rw [← d_eq_bd, ← HomologicalComplex.toCycles_i]
  have hy' : (toCycles A (m + 2) (m + 1)).hom y = ∑ i, n i • c i := hy
  show (iCycles A (m + 1)).hom ((toCycles A (m + 2) (m + 1)).hom y) = _
  rw [hy', map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, Int.cast_smul_eq_zsmul]
  exact congrArg _ (hc i)

theorem SRel_of : SRel := by
  intro l ν e hl
  obtain ⟨n, t, h1, h2⟩ := rel_bd (ZMod (l ^ ν)) (Cq (l ^ ν) × Cq (l ^ ν)) (2 * e + 1) (2 * e + 3) l hl.out.two_le
    (gen_two (l ^ ν) (l ^ ν) (e + 1))
    (fun t => cm (ZMod (l ^ ν)) (dt (l ^ ν) t) _ (zc (l ^ ν) e)) (fun t => by
      have h0 : bd _ _ _ (zc (l ^ ν) e) = 0 := LateralTheory.Q.SZcT.SZc_of (l ^ ν) e
      unfold Cyc
      rw [(LateralTheory.Q.SChainPf.SChain_of _).2.1, h0, map_zero])
  refine ⟨fun t => (n t : ZMod (l ^ ν)), t, ?_, h2⟩
  rw [ZMod.coe_int_isUnit_iff_isCoprime, Nat.cast_pow]
  exact ((Nat.prime_iff_prime_int.1 hl.out).irreducible.coprime_iff_not_dvd.2 h1).pow_left

end LateralTheory.Q.SRelT
end
