import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwBernHk
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwBernFaith
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkBern
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkEv
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkTrace
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwBruhatKO
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwMemIwC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHeckePairIwC
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemFixedPiIff
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem dc_apply {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K K' : Subgroup H) (x : H) (h : FinOrb K K' x) (m : M) :
    dc ρ K K' x m = ∑ᶠ q : MulAction.orbit K (x : H ⧸ K'), ρ (q : H ⧸ K').out m := by
  have : Finite (MulAction.orbit K (x : H ⧸ K')) := h
  have := Fintype.ofFinite (MulAction.orbit K (x : H ⧸ K'))
  rw [dc, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, LinearMap.sum_apply]

private theorem relIndex_ne {H : Type} [Group H] (K I : Subgroup H) (h : FinOrb K I 1) : I.relIndex K ≠ 0 := by
  have e : I.subgroupOf K = MulAction.stabilizer K ((1 : H) : H ⧸ I) := by
    ext g
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
    change _ ↔ (g : H) ∈ MulAction.stabilizer H ((1 : H) : H ⧸ I)
    rw [MulAction.stabilizer_quotient]
  rw [Subgroup.relIndex, e, MulAction.index_stabilizer]
  exact Set.ncard_ne_zero_of_mem (MulAction.mem_orbit_self _) h

private theorem bern_ev {O H E : Type} [CommRing O] [IsDomain O] [Ring H] [Algebra O H] [Ring E] [Algebra O E] {n : ℕ} {q : O}
    (b : Hk.Bern n q H) (hF : b.Faithful) (ev : H →ₐ[O] E) :
    (∀ z : MvPolynomial (Fin n) O, z.IsSymmetric → ev b.one * ev.comp b.th z = ev.comp b.th z * ev b.one) ∧
      (∀ (ι : Type) [Fintype ι] (a c : ι → MvPolynomial (Fin n) O), Hk.IsDual a c →
        ∑ i, ev.comp b.th (a i) * ev b.one * ev.comp b.th (c i) = ev.comp b.th (Hk.NN n q)) ∧
      ∀ y, ev b.one * ev.comp b.th y * ev b.one = ev.comp b.th (Hk.dd (Hk.NN n q * y)) * ev b.one := by
  refine ⟨fun z hz => ?_, fun ι _ a c hd => ?_, fun y => ?_⟩
  · simp only [AlgHom.comp_apply, ← map_mul]
    congr 1
    rw [Hk.Bern.one, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => (hkBern O n _ _ b).2 z hz w
  · simp only [AlgHom.comp_apply, ← map_mul, ← map_sum]
    rw [hkSum O n _ _ b hF ι a c hd]
  · simp only [AlgHom.comp_apply]
    rw [← map_mul, ← map_mul, hkSandwich O n _ _ b hF y, map_mul]

private theorem ev_rel {O H E : Type} [CommRing O] [Ring H] [Algebra O H] [Ring E] [Algebra O E] (ev : H →ₐ[O] E)
    {a y z : H} {c : O} {y' z' : E} (h : a * y = c • z) (hy : ev y = y') (hz : ev z = z') : ev a * y' = c • z' := by
  rw [← hy, ← hz, ← map_mul, h, map_smul]

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem bruh : ∀ g ∈ KO k (Fin n), ∃! w : Equiv.Perm (Fin n),
    ∃ a ∈ iwC k n ⊤, ∃ b ∈ iwC k n ⊤, g = a * pm k n w * b := by
  rw [(memIwC k n ⊤).2.1]
  exact (bruhatKO k n).2

private theorem iw_le : iwC k n ⊤ ≤ KO k (Fin n) := by
  rw [(memIwC k n ⊤).2.1]
  exact iwahori_le_KO k (Fin n)

private theorem dom_fund {x : kˣ} (hx : IsUnif x) (m : ℕ) : Dom (fun j : Fin n => x ^ fund n m j) := by
  have hx1 : valuation k (x : k) ≤ 1 := by
    obtain ⟨p, -, hp⟩ := hx
    rw [← hp]
    exact p.2
  intro j l hjl
  have hjl' : (j : ℕ) ≤ (l : ℕ) := hjl
  simp only [fund]
  by_cases h1 : (l : ℕ) < m
  · have h2 : (j : ℕ) < m := lt_of_le_of_lt hjl' h1
    simp [h1, h2]
  · by_cases h2 : (j : ℕ) < m
    · simpa [h1, h2] using hx1
    · simp [h1, h2]

private theorem fund_split {T : Type} [CommGroup T] (x : T) (i : Fin n) : (fun j : Fin n => x ^ fund n ((i : ℕ) + 1) j)
    = Pi.mulSingle i x * (fun j : Fin n => x ^ fund n (i : ℕ) j) := by
  funext j
  simp only [fund, Pi.mul_apply]
  by_cases hj : j = i
  · subst hj
    simp
  · have hne : (j : ℕ) ≠ (i : ℕ) := fun h => hj (Fin.ext h)
    rw [Pi.mulSingle_eq_of_ne hj, one_mul]
    by_cases h : (j : ℕ) < (i : ℕ)
    · have h' : (j : ℕ) < (i : ℕ) + 1 := by omega
      simp [h, h']
    · have h' : ¬ (j : ℕ) < (i : ℕ) + 1 := by omega
      simp [h, h']

private theorem dc_K {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M) :
    (∀ m ∈ fixd ρ (iwC k n ⊤), dc ρ (KO k (Fin n)) (iwC k n ⊤) 1 m ∈ fixd ρ (KO k (Fin n))) ∧
    ∀ m ∈ fixd ρ (KO k (Fin n)),
      dc ρ (KO k (Fin n)) (iwC k n ⊤) 1 m = ((iwC k n ⊤).relIndex (KO k (Fin n))) • m := by
  obtain ⟨hf, -, h3⟩ := hkTrace A _ M ρ _ _ iw_le _ (pm k n) (heckePairIwC k n ⊤).1 (bruhatKO k n).1 bruh
  have ha := (hkApply A _ M ρ _ _ 1 hf).1
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · rw [← ha ⟨m, hm⟩]
    exact Subtype.property _
  · have h := congrArg Subtype.val (h3 ⟨m, hm⟩)
    rw [trc, ha, Submodule.coe_smul, Nat.cast_smul_eq_nsmul] at h
    exact h

private theorem locO (O M : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    (ρ : Representation O (GL (Fin n) k) M) {x : kˣ} (hx : IsUnif x) (hq : IsUnit (resCard k : O)) :
    ∃ (th : MvPolynomial (Fin n) O →ₐ[O] Module.End O (fixd ρ (iwC k n ⊤))) (E : Module.End O (fixd ρ (iwC k n ⊤))),
      (∀ v, (E v : M) = dc ρ (KO k (Fin n)) (iwC k n ⊤) 1 v) ∧
      (∀ i : Fin n, th (MvPolynomial.X i) * hk ρ (iwC k n ⊤) (pw x (fund n i)) =
        ((resCard k : O) ^ (i : ℕ)) • hk ρ (iwC k n ⊤) (pw x (fund n ((i : ℕ) + 1)))) ∧
      (∀ z : MvPolynomial (Fin n) O, z.IsSymmetric → E * th z = th z * E) ∧
      (∀ (ι : Type) [Fintype ι] (a b : ι → MvPolynomial (Fin n) O), Hk.IsDual a b →
        ∑ i, th (a i) * E * th (b i) = th (Hk.NN n (resCard k : O))) ∧
      ∀ y, E * th y * E = th (Hk.dd (Hk.NN n (resCard k : O) * y)) * E := by
  obtain ⟨b, hT, hX⟩ := bernHk k n O x hx hq
  have hF := bernFaith k n O x hx hq b hT hX
  obtain ⟨ev, hev⟩ := hkEv O _ M ρ _ (heckePairIwC k n ⊤).1
  obtain ⟨hf, h2, -⟩ := hkTrace O _ M ρ _ _ iw_le _ (pm k n) (heckePairIwC k n ⊤).1 (bruhatKO k n).1 bruh
  obtain ⟨g1, g2, g3⟩ := bern_ev b hF ev
  refine ⟨ev.comp b.th, ev b.one, fun v => ?_, fun i => ?_, g1, g2, g3⟩
  · have h : ev b.one = ∑ w, hk ρ (iwC k n ⊤) (pm k n w) :=
      (map_sum ev b.T Finset.univ).trans (Finset.sum_congr rfl fun w _ => (congrArg ev (hT w)).trans (hev _))
    rw [h, h2]
    exact (hkApply O _ M ρ _ _ 1 hf).1 v
  · exact ev_rel ev (hX i) (hev _) (hev _)

private theorem locA (O A M V : Type) [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [AddCommGroup M] [Module A M]
    [AddCommGroup V] [Module A V] (ρ : Representation A (GL (Fin n) k) M) {x : kˣ} (hx : IsUnif x)
    (hq : IsUnit (resCard k : O)) (tf : ∀ (c : ℕ) (m : M), c ≠ 0 → c • m = 0 → m = 0)
    (ι : V →ₗ[A] M) (hι : Function.Injective ι) (hI : ∀ v, ι v ∈ fixd ρ (iwC k n ⊤))
    (Θ : (Fin n → kˣ) →* (Module.End A V)ˣ)
    (hΘ : ∀ t, Dom t → ∀ v, ι ((Θ t).val v) = dc ρ (iwC k n ⊤) (iwC k n ⊤) (diagT k (Fin n) t) (ι v))
    (e : Module.End A V) (he : ∀ v, ι (e v) = dc ρ (KO k (Fin n)) (iwC k n ⊤) 1 (ι v))
    (φ : MvPolynomial (Fin n) O →+* Module.End A V)
    (hC : ∀ o v, φ (MvPolynomial.C o) v = algebraMap O A o • v)
    (hφ : ∀ i, φ (MvPolynomial.X i) = ((resCard k : A) ^ (i : ℕ)) • (Θ (Pi.mulSingle i x)).val) :
    (∀ z : MvPolynomial (Fin n) O, z.IsSymmetric → Commute e (φ z)) ∧
      (∀ (J : Type) [Fintype J] (a b : J → MvPolynomial (Fin n) O), Hk.IsDual a b →
        ∑ i, φ (a i) * e * φ (b i) = φ (Hk.NN n (resCard k : O))) ∧
      ∀ y v, ι v ∈ fixd ρ (KO k (Fin n)) → e (φ y v) = φ (Hk.dd (Hk.NN n (resCard k : O) * y)) v := by
  letI : Module O M := Module.compHom M (algebraMap O A)
  have hs : ∀ (o : O) (m : M), o • m = algebraMap O A o • m := fun _ _ => rfl
  let ρO : Representation O (GL (Fin n) k) M :=
    { toFun := fun g => { toFun := ρ g, map_add' := map_add _, map_smul' := fun o m => map_smul (ρ g) (algebraMap O A o) m }
      map_one' := LinearMap.ext fun m => LinearMap.congr_fun (map_one ρ) m
      map_mul' := fun g h => LinearMap.ext fun m => LinearMap.congr_fun (map_mul ρ g h) m }
  have hdc : ∀ K K' g, FinOrb K K' g → ∀ m, dc ρO K K' g m = dc ρ K K' g m := fun K K' g h m => by
    rw [dc_apply _ _ _ _ h, dc_apply _ _ _ _ h]; rfl
  obtain ⟨th, E, hE, hX, hsym, hsum, hsw⟩ := locO O M ρO hx hq
  have hP := heckePairIwC k n ⊤
  let j : V →+ fixd ρO (iwC k n ⊤) := ⟨⟨fun v => ⟨ι v, hI v⟩, Subtype.ext (map_zero ι)⟩, fun a b => Subtype.ext (map_add ι a b)⟩
  have hj : ∀ v, (j v : M) = ι v := fun _ => rfl
  have jinj : Function.Injective j := fun a b h => hι (congrArg Subtype.val h)
  have je : ∀ v, j (e v) = E (j v) := fun v => Subtype.ext (by rw [hE, hj, hj, he, hdc _ _ _ (hP.2.2 ⊤).2])
  have jΘ : ∀ m v, j ((Θ fun a => x ^ fund n m a).val v) = hk ρO (iwC k n ⊤) (pw x (fund n m)) (j v) := fun m v =>
    Subtype.ext (by
      rw [hj, hΘ _ (dom_fund hx m), ← hdc _ _ _ (hP.1 _)]
      exact ((hkApply O _ M ρO _ _ _ (hP.1 _)).1 (j v)).symm)
  have jX : ∀ i v, j (φ (MvPolynomial.X i) v) = th (MvPolynomial.X i) (j v) := by
    intro i v
    obtain ⟨u, rfl⟩ := ((Module.End.isUnit_iff _).1 (Θ fun a => x ^ fund n i a).isUnit).2 v
    have h := LinearMap.congr_fun (hX i) (j u)
    rw [Module.End.mul_apply, ← jΘ, LinearMap.smul_apply, ← jΘ, fund_split, map_mul, Units.val_mul,
      Module.End.mul_apply] at h
    rw [h, hφ]
    apply Subtype.ext
    rw [hj, LinearMap.smul_apply, map_smul, Submodule.coe_smul, hs, map_pow, map_natCast, hj]
  have jφ : ∀ z v, j (φ z v) = th z (j v) := by
    intro z
    induction z using MvPolynomial.induction_on with
    | C o =>
      intro v
      apply Subtype.ext
      rw [hC, hj, map_smul, ← MvPolynomial.algebraMap_eq, th.commutes, Module.algebraMap_end_apply, Submodule.coe_smul, hs, hj]
    | add p q hp hq => intro v; simp only [map_add, LinearMap.add_apply, hp, hq]
    | mul_X p i hp => intro v; simp only [map_mul, Module.End.mul_apply, hp, jX]
  refine ⟨fun z hz => LinearMap.ext fun v => jinj ?_, fun J _ a b hd => LinearMap.ext fun v => jinj ?_, fun y v hv => ?_⟩
  · simp only [Module.End.mul_apply, je, jφ]
    exact LinearMap.congr_fun (hsym z hz) _
  · rw [jφ, ← hsum J a b hd]
    simp only [LinearMap.sum_apply, map_sum, Module.End.mul_apply, je, jφ]
  · have h1 : e v = ((iwC k n ⊤).relIndex (KO k (Fin n))) • v := hι (by rw [he, map_nsmul, (dc_K ρ).2 _ hv])
    have h2 : e (φ y (e v)) = φ (Hk.dd (Hk.NN n (resCard k : O) * y)) (e v) := jinj (by
      simp only [je, jφ]
      exact LinearMap.congr_fun (hsw y) _)
    rw [h1, map_nsmul, map_nsmul, map_nsmul, ← sub_eq_zero, ← nsmul_sub] at h2
    apply hι
    rw [← sub_eq_zero, ← map_sub]
    refine tf _ _ (relIndex_ne _ _ (hP.2.2 ⊤).2) ?_
    rw [← map_nsmul, h2, map_zero]

end Loc

private theorem comm_dc {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K K' : Subgroup H) (x : H) (φ : Module.End A M) (h : ∀ g, Commute φ (ρ g)) :
    Commute φ (dc ρ K K' x) :=
  finsum_induction (fun e => Commute φ e) (Commute.zero_right φ) (fun _ _ h1 h2 => h1.add_right h2) fun _ => h _

private theorem lprod_mem {A V : Type} [CommRing A] [AddCommGroup V] [Module A V] (W : Submodule A V) (f : Module.End A V)
    (hf : ∀ v, f v ∈ W) (s : List (Module.End A V)) (hs : ∀ a ∈ s, ∀ v ∈ W, a v ∈ W) (h : f ∈ s) (v : V) : s.prod v ∈ W := by
  induction s with
  | nil => simp at h
  | cons a s ih =>
    rw [List.prod_cons, Module.End.mul_apply]
    rcases List.mem_cons.1 h with rfl | h'
    · exact hf _
    · exact hs a List.mem_cons_self _ (ih (fun b hb => hs b (List.mem_cons_of_mem _ hb)) h')

private theorem comm_unit {R : Type} [Monoid R] {e : R} {u v w : Rˣ} (h : w = u * v) (hw : Commute e w) (hv : Commute e v) :
    Commute e u := by
  have : u = w * v⁻¹ := by rw [h, mul_inv_cancel_right]
  rw [this, Units.val_mul]
  exact hw.mul_right hv.units_inv_right

private theorem stab {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M)
    (K : Subgroup G) (tf : ∀ (k : ℕ) (m : M), k ≠ 0 → k • m = 0 → m = 0) (U : Submodule A M) (e f : Module.End A U) (r : ℕ)
    (hr : r ≠ 0) (eK : ∀ v, (e v : M) ∈ fixd ρ K) (hf : Commute e f) (v : U) (h1 : (e v : M) = r • (v : M)) :
    (f v : M) ∈ fixd ρ K := by
  intro g hg
  have h1' : e v = r • v := Subtype.ext h1
  have h2 := eK (f v) g hg
  have h3 : e (f v) = r • f v := by
    rw [← map_nsmul, ← h1']
    exact LinearMap.congr_fun hf.eq v
  rw [h3, Submodule.coe_smul_of_tower, map_nsmul, ← sub_eq_zero, ← nsmul_sub] at h2
  exact sub_eq_zero.1 (tf r _ hr h2)

private theorem comm_res {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {U : Submodule A M}
    {e f : Module.End A U} {e' f' : Module.End A M} (he : ∀ v, (e v : M) = e' v) (hf : ∀ v, (f v : M) = f' v)
    (h : Commute e' f') : Commute e f := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, he, hf, hf, he]
  exact LinearMap.congr_fun h.eq _

private theorem emb_C {O A V : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup V] [Module A V] {q n : ℕ}
    (act : PU A q n →ₐ[A] Module.End A V) (j : Fin q) (o : O) (v : V) :
    (act.toRingHom.comp (emb O A j)) (MvPolynomial.C o) v = algebraMap O A o • v := by
  have : emb O A (q := q) (n := n) j (MvPolynomial.C o) = algebraMap A _ (algebraMap O A o) := by simp [emb]
  exact (congrArg (fun p => act p v) this).trans (LinearMap.congr_fun (act.commutes _) v)

private theorem emb_X {O A V : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup V] [Module A V] {q n : ℕ}
    (act : PU A q n →ₐ[A] Module.End A V) (j : Fin q) (i : Fin n) :
    (act.toRingHom.comp (emb O A j)) (MvPolynomial.X i) = act (MvPolynomial.X (j, i)) := by
  have : emb O A (q := q) (n := n) j (MvPolynomial.X i) = MvPolynomial.X (j, i) := by simp [emb]
  exact congrArg act this

section

variable {L : Type} [Field L] [NumberField L] {n q : ℕ} {w : Fin q → Plc L} {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
  (ρ : Representation A (GV n w) M)

private theorem comm_at {j j' : Fin q} (h : j ≠ j') (g : GLw n (w j)) (g' : GLw n (w j')) :
    Commute (ρ (atJ n w j g)) (ρ (atJ n w j' g')) :=
  (Pi.mulSingle_commute (f := fun j => GLw n (w j)) h g g').map ρ

private theorem comm_dd {j j' : Fin q} (h : j ≠ j') (K K' : Subgroup (GLw n (w j))) (g : GLw n (w j))
    (I I' : Subgroup (GLw n (w j'))) (g' : GLw n (w j')) :
    Commute (dc (ρ.comp (atJ n w j)) K K' g) (dc (ρ.comp (atJ n w j')) I I' g') :=
  comm_dc _ _ _ _ _ fun a' => (comm_dc _ _ _ _ _ fun a => comm_at ρ (Ne.symm h) a' a).symm

private theorem mem_pi (H : ∀ j, Subgroup (GLw n (w j))) (m : M) :
    m ∈ fixd ρ (Subgroup.pi Set.univ H) ↔ ∀ j, m ∈ fixd (ρ.comp (atJ n w j)) (H j) :=
  by apply _root_.UpperTheory.Reformulated.B.Gr29.mem_pi <;> assumption

private theorem pres (j : Fin q) : ∀ m ∈ fixd ρ (UC n w fun _ => ⊤),
    dc (ρ.comp (atJ n w j)) (KO _ (Fin n)) (iwC _ n ⊤) 1 m ∈ fixd ρ (UC n w fun _ => ⊤) := by
  intro m hm
  rw [UC, mem_pi] at hm ⊢
  intro j'
  by_cases e : j' = j
  · subst e
    exact fixd_anti _ iw_le ((dc_K _).1 m (hm _))
  · intro u hu
    have h1 := LinearMap.congr_fun (comm_dc (ρ.comp (atJ n w j)) (KO _ (Fin n)) (iwC _ n ⊤) 1 _
      fun g' => comm_at ρ e u g').eq m
    rw [Module.End.mul_apply, Module.End.mul_apply, show ρ (atJ n w j' u) m = m from hm j' u hu] at h1
    exact h1

private theorem memI (j : Fin q) (v : fixd ρ (UC n w fun _ => ⊤)) : (v : M) ∈ fixd (ρ.comp (atJ n w j)) (iwC _ n ⊤) :=
  (mem_pi ρ _ _).1 v.2 j

variable {ρ} {e : Fin q → Module.End A (fixd ρ (UC n w fun _ => ⊤))}
  (he : ∀ j v, (e j v : M) = dc (ρ.comp (atJ n w j)) (KO _ (Fin n)) (iwC _ n ⊤) 1 v)

include he

private theorem e_K (j : Fin q) (v : fixd ρ (UC n w fun _ => ⊤)) : (e j v : M) ∈ fixd (ρ.comp (atJ n w j)) (KO _ (Fin n)) := by
  rw [he]; exact (dc_K _).1 _ (memI ρ j v)

private theorem e_e (j j' : Fin q) : Commute (e j) (e j') := by
  by_cases h : j = j'
  · subst h; exact Commute.refl _
  · exact comm_res (he j) (he j') (comm_dd ρ h _ _ _ _ _ _)

private theorem fixed_vectors_stable_under_hecke_action (tf : ∀ (k : ℕ) (m : M), k ≠ 0 → k • m = 0 → m = 0) (j : Fin q)
    (f : Module.End A (fixd ρ (UC n w fun _ => ⊤))) (hf : Commute (e j) f) :
    ∀ v ∈ (fixd (ρ.comp (atJ n w j)) (KO _ (Fin n))).comap (fixd ρ (UC n w fun _ => ⊤)).subtype,
      f v ∈ (fixd (ρ.comp (atJ n w j)) (KO _ (Fin n))).comap (fixd ρ (UC n w fun _ => ⊤)).subtype := fun v hv =>
  stab _ _ tf _ (e j) f _ (relIndex_ne _ _ ((heckePairIwC _ n ⊤).2.2 ⊤).2) (e_K he j) hf v
    ((he j v).trans ((dc_K _).2 _ hv))

private theorem e_X {l : ℕ} {x δ : ∀ j, ((w j).adicCompletion L)ˣ} (T : ThData l ρ x δ) (hx : ∀ j, IsUnif (x j))
    (j j' : Fin q) (i : Fin n) (h : j ≠ j') : Commute (e j) (T.actw (MvPolynomial.X (j', i))) := by
  have eΘ : ∀ t, Dom t → Commute (e j) (T.Θw j' t).val := fun t ht =>
    comm_res (he j) (T.hw.1 j' t ht) (comm_dd ρ h _ _ _ _ _ _)
  rw [T.actw_u]
  exact Commute.smul_right (comm_unit ((congrArg (T.Θw j') (fund_split (x j') i)).trans (map_mul _ _ _))
    (eΘ _ (dom_fund (hx j') _)) (eΘ _ (dom_fund (hx j') _))) _

private theorem e_prod (tf : ∀ (k : ℕ) (m : M), k ≠ 0 → k • m = 0 → m = 0) (v : fixd ρ (UC n w fun _ => ⊤)) :
    ((List.ofFn e).prod v : M) ∈ fixd ρ (UK n w) := by
  refine (mem_pi ρ _ _).2 fun j => ?_
  refine lprod_mem ((fixd (ρ.comp (atJ n w j)) (KO _ (Fin n))).comap (fixd ρ (UC n w fun _ => ⊤)).subtype) (e j) (e_K he j) _
    (fun a ha => ?_) (List.mem_ofFn.2 ⟨j, rfl⟩) v
  obtain ⟨j', rfl⟩ := List.mem_ofFn.1 ha
  exact fixed_vectors_stable_under_hecke_action he tf j _ (e_e he j j')

end

theorem UpperTheory.V.Pa.Lev.hkHypOf :
    ∀ (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L) (l : ℕ) (O A M : Type) [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] [AddCommGroup M] [Module A M] (ρ : Representation A (GV n w) M) (x δ : ∀ j, ((w j).adicCompletion L)ˣ) (T : ThData l ρ x δ), (∀ j, IsUnif (x j)) → (∀ j, IsUnit (qj w j : O)) → (∀ (k : ℕ) (m : M), k ≠ 0 → k • m = 0 → m = 0) → ∃ e : Fin q → Module.End A (fixd ρ (UC n w fun _ => ⊤)), HkHyp O (qj w) T.actw e (fun j => (fixd (ρ.comp (atJ n w j)) (KO _ (Fin n))).comap (fixd ρ (UC n w fun _ => ⊤)).subtype) ∧ ∀ v, ((List.ofFn e).prod v : M) ∈ fixd ρ (UK n w) := by
  intro L _ _ n q w l O A M _ _ _ _ _ _ ρ x δ T hx hq tf
  obtain ⟨e, he⟩ : ∃ e : Fin q → Module.End A (fixd ρ (UC n w fun _ => ⊤)), ∀ j v,
      (e j v : M) = dc (ρ.comp (atJ n w j)) (KO _ (Fin n)) (iwC _ n ⊤) 1 v :=
    ⟨fun j => LinearMap.restrict _ (pres ρ j), fun _ _ => rfl⟩
  have hloc := fun j => locA O A M (fixd ρ (UC n w fun _ => ⊤)) (ρ.comp (atJ n w j)) (hx j) (hq j) tf
    (fixd ρ (UC n w fun _ => ⊤)).subtype Subtype.val_injective (memI ρ j) (T.Θw j) (T.hw.1 j) (e j) (he j)
    (T.actw.toRingHom.comp (emb O A j)) (emb_C _ j) (fun i => (emb_X _ j i).trans (T.actw_u j i))
  exact ⟨e, ⟨e_e he, e_X he T hx, fun j => (hloc j).1, fun j => (hloc j).2.1,
    fun j j' i h => fixed_vectors_stable_under_hecke_action he tf j _ (e_X he T hx j j' i h),
    fun j j' _ => fixed_vectors_stable_under_hecke_action he tf j _ (e_e he j j'), fun j => (hloc j).2.2⟩, e_prod he tf⟩
