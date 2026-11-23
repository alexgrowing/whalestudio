import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane

noncomputable section

namespace PositivityTheory.HtPt.Twomega

open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT

section Complete

variable {p : ℕ} {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]

theorem cong_iff {ι : Type} [Finite ι] (b : Module.Basis ι O M) (n : ℕ) (w w' : M) :
    (∃ u : M, w' = w + (p ^ n) • u) ↔ ∀ i, (p : O) ^ n ∣ b.equivFun w' i - b.equivFun w i := by
  constructor
  · rintro ⟨u, rfl⟩ i
    refine ⟨b.equivFun u i, ?_⟩
    rw [map_add, map_nsmul, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow, add_sub_cancel_left]
  · intro h
    choose c hc using h
    refine ⟨b.equivFun.symm c, b.equivFun.injective (funext fun i => ?_)⟩
    rw [map_add, map_nsmul, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Nat.cast_pow,
      LinearEquiv.apply_symm_apply, ← hc, add_sub_cancel]

theorem smod_iff (n : ℕ) (a b : O) :
    a ≡ b [SMOD (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O O)] ↔ (p : O) ^ n ∣ b - a := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    dvd_sub_comm]

theorem eq_zero_of_cong [Module.Free O M] [Module.Finite O M] (hO : IsAdicComplete (Ideal.span {(p : O)}) O)
    (w : M) (h : ∀ n, ∃ u : M, w = 0 + (p ^ n) • u) : w = 0 := by
  let b := Module.Free.chooseBasis O M
  refine b.equivFun.injective (funext fun i => ?_)
  refine (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : O)})).2 fun n => SModEq.symm ?_
  exact (smod_iff n _ _).2 ((cong_iff b n 0 w).1 (h n) i)

theorem exists_lim [Module.Free O M] [Module.Finite O M] (hO : IsAdicComplete (Ideal.span {(p : O)}) O)
    (w : ℕ → M) (h : ∀ n, ∃ u : M, w (n + 1) = w n + (p ^ n) • u) :
    ∃ W : M, ∀ n, ∃ u : M, W = w n + (p ^ n) • u := by
  let b := Module.Free.chooseBasis O M
  have key : ∀ i, ∃ c : O, ∀ n, (p : O) ^ n ∣ c - b.equivFun (w n) i := by
    intro i
    have h1 : ∀ n, b.equivFun (w n) i ≡ b.equivFun (w (n + 1)) i
        [SMOD (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O O)] :=
      fun n => (smod_iff n _ _).2 ((cong_iff b n _ _).1 (h n) i)
    obtain ⟨c, hc⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : O)}) (fun n => b.equivFun (w n) i)
      fun {m n} hmn => by
        induction n, hmn using Nat.le_induction with
        | base => rfl
        | succ n hmn ih =>
          exact ih.trans ((h1 n).mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn)))
    exact ⟨c, fun n => (smod_iff n _ _).1 (hc n)⟩
  choose c hc using key
  exact ⟨b.equivFun.symm c, fun n => (cong_iff b n _ _).2 fun i => by
    rw [LinearEquiv.apply_symm_apply]; exact hc i n⟩

end Complete

variable {p : ℕ} {O : Type} [CommRing O] {La : Type} [AddCommGroup La]
  {L : Type} [AddCommGroup L] [Module O L] (X : OrdTower p O La L)

theorem der_smul (n : ℕ) (r : O) (f : LevGrp La p n → O) (w : Module.Dual O L) (h : X.der n f w) :
    X.der n (r • f) (r • w) := by
  have := X.der_mul n _ _ _ _ (X.der_const n r) h
  rw [smul_zero, add_zero] at this
  exact this

theorem der_sub (n : ℕ) (f g : LevGrp La p n → O) (w w' : Module.Dual O L) (h : X.der n f w)
    (h' : X.der n g w') : X.der n (f - g) (w - w') := by
  have := X.der_add n _ _ _ _ h (der_smul X n (-1) g w' h')
  simpa only [neg_smul, one_smul, ← sub_eq_add_neg] using this

theorem der_of_mem_sq (n : ℕ) (f : X.A n) (hf : f ∈ BT.augIdeal (X.A n) ^ 2) : X.der n f.1 0 := by
  rw [sq] at hf
  refine Submodule.mul_induction_on hf (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · obtain ⟨w, hw⟩ := X.der_ex n a.1 a.2
    obtain ⟨w', hw'⟩ := X.der_ex n b.1 b.2
    have ha0 : a.1 1 = 0 := ha
    have hb0 : b.1 1 = 0 := hb
    have := X.der_mul n _ _ _ _ hw hw'
    rw [ha0, hb0, zero_smul, zero_smul, add_zero] at this
    exact this
  · have := X.der_add n _ _ _ _ ha hb
    rw [add_zero] at this
    exact this

variable [Fact p.Prime] {X} {G : PDivGroup p O} {e : ∀ n, G.A n ≃ₐ[O] X.A n} {τ : La →+ G.Tate}

theorem counit_eq (hre : X.Realises G e τ) (n : ℕ) (a : G.A n) :
    Bialgebra.counitAlgHom O (G.A n) a = (e n a).1 1 := by
  have h := hre.pt 0 n a
  rw [map_zero] at h
  exact h

theorem map_ker (hre : X.Realises G e τ) (n : ℕ) :
    (BT.augIdeal (X.A n)).comap (e n) = RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) := by
  ext a
  rw [Ideal.mem_comap, OrderApi.mem_augIdeal, RingHom.mem_ker, counit_eq hre]

theorem mem_sq_iff (hre : X.Realises G e τ) (n : ℕ) (a : G.A n) :
    a ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) ^ 2 ↔ e n a ∈ BT.augIdeal (X.A n) ^ 2 := by
  have h : (RingHom.ker (Bialgebra.counitAlgHom O (G.A n))).map (e n) = BT.augIdeal (X.A n) := by
    rw [← map_ker hre, Ideal.map_comap_of_surjective _ (e n).surjective]
  rw [← h, ← Ideal.map_pow]
  constructor
  · exact Ideal.mem_map_of_mem _
  · intro h1
    obtain ⟨b, hb, hab⟩ := (Ideal.mem_map_iff_of_surjective _ (e n).surjective).1 h1
    rwa [← (e n).injective hab]

theorem dUnit_eq_zero_iff (hre : X.Realises G e τ) (n : ℕ) (a : G.A n) :
    dUnit O a = 0 ↔ X.der n (e n a).1 0 := by
  rw [dUnit, AugCot.d_eq_zero_iff, mem_sq_iff hre, map_sub, AlgEquiv.commutes]
  set c := Bialgebra.counitAlgHom O (G.A n) a with hc
  have hc' : X.der n (algebraMap O (X.A n) c).1 0 := X.der_const n c
  constructor
  · intro h
    have := X.der_add n _ _ _ _ (der_of_mem_sq X n _ h) hc'
    simpa using this
  · intro h
    have h1 := der_sub X n _ _ _ _ h hc'
    rw [sub_zero] at h1
    refine X.der_zero n ⟨e n a - algebraMap O (X.A n) c, ?_⟩ h1
    rw [OrderApi.mem_augIdeal, hc, counit_eq hre]
    exact sub_self _

theorem dUnit_eq_iff (hre : X.Realises G e τ) (n : ℕ) (a b : G.A n) (w : Module.Dual O L)
    (h : X.der n (e n a).1 w) : dUnit O b = dUnit O a ↔ X.der n (e n b).1 w := by
  rw [← sub_eq_zero, dUnit, dUnit, ← map_sub]
  refine (dUnit_eq_zero_iff hre n (b - a)).trans ?_
  rw [map_sub]
  constructor
  · intro h1
    have := X.der_add n _ _ _ _ h1 h
    simpa using this
  · intro h1
    have := der_sub X n _ _ _ _ h1 h
    rw [sub_self] at this
    exact this

omit [Fact p.Prime] in
theorem exists_der (e : ∀ n, G.A n ≃ₐ[O] X.A n) (n : ℕ) (w : Module.Dual O L) :
    ∃ a : G.A n, X.der n (e n a).1 w := by
  obtain ⟨f, hf, h⟩ := X.der_onto n w
  exact ⟨(e n).symm ⟨f, hf⟩, by rwa [AlgEquiv.apply_symm_apply]⟩

def cls (e : ∀ n, G.A n ≃ₐ[O] X.A n) (n : ℕ) (w : Module.Dual O L) : Cot O (G.A n) :=
  dUnit O (exists_der e n w).choose

theorem dUnit_eq_cls (hre : X.Realises G e τ) (n : ℕ) (a : G.A n) (w : Module.Dual O L) :
    dUnit O a = cls e n w ↔ X.der n (e n a).1 w :=
  dUnit_eq_iff hre n _ a w (exists_der e n w).choose_spec

theorem der_res (hre : X.Realises G e τ) (n : ℕ) (a : G.A (n + 1)) (w : Module.Dual O L)
    (h : X.der (n + 1) (e (n + 1) a).1 w) : X.der n (e n (G.res n a)).1 w :=
  X.der_res n _ _ w h (hre.res n a)

def toOmega (hre : X.Realises G e τ) : Module.Dual O L →ₗ[O] G.omega where
  toFun w := ⟨fun n => cls e n w, fun n => by
    obtain ⟨a, ha⟩ := exists_der e (n + 1) w
    change cotMap (G.res n) (cls e (n + 1) w) = cls e n w
    rw [← (dUnit_eq_cls hre _ a w).2 ha, cotMap_d, dUnit_eq_cls hre]
    exact der_res hre n a w ha⟩
  map_add' w w' := Subtype.ext (funext fun n => by
    obtain ⟨a, ha⟩ := exists_der e n w
    obtain ⟨b, hb⟩ := exists_der e n w'
    change cls e n (w + w') = cls e n w + cls e n w'
    rw [← (dUnit_eq_cls hre _ a w).2 ha, ← (dUnit_eq_cls hre _ b w').2 hb, dUnit, dUnit, ← map_add, eq_comm]
    refine (dUnit_eq_cls hre _ _ _).2 ?_
    rw [map_add]
    exact X.der_add n _ _ _ _ ha hb)
  map_smul' r w := Subtype.ext (funext fun n => by
    obtain ⟨a, ha⟩ := exists_der e n w
    change cls e n (r • w) = r • cls e n w
    rw [← (dUnit_eq_cls hre _ a w).2 ha, dUnit, ← map_smul, eq_comm]
    refine (dUnit_eq_cls hre _ _ _).2 ?_
    rw [map_smul]
    exact der_smul X n r _ _ ha)

theorem toOmega_val (hre : X.Realises G e τ) (w : Module.Dual O L) (n : ℕ) :
    (toOmega hre w).1 n = cls e n w := rfl

theorem toOmega_bijective (hO : IsAdicComplete (Ideal.span {(p : O)}) O) [Module.Free O L] [Module.Finite O L]
    (hre : X.Realises G e τ) : Function.Bijective (toOmega hre) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro w hw
    refine eq_zero_of_cong hO w fun n => ?_
    have h0 : dUnit O (0 : G.A n) = 0 := map_zero _
    have h1 : cls e n w = 0 := congrArg (fun x : G.omega => x.1 n) hw
    exact (X.der_unique n _ 0 w ((dUnit_eq_zero_iff hre n 0).1 h0)).1
      ((dUnit_eq_cls hre n 0 w).1 (h0.trans h1.symm))
  · intro ω
    choose a ha using fun n => AugCot.d_surjective _ (ω.1 n)
    choose w hw using fun n => X.der_ex n (e n (a n)).1 (e n (a n)).2
    obtain ⟨W, hW⟩ := exists_lim hO w fun n => by
      refine (X.der_unique n _ _ _ (hw n)).1 ?_
      refine (dUnit_eq_iff hre n _ _ _ (der_res hre n _ _ (hw (n + 1)))).1 ?_
      rw [← cotMap_d, dUnit, dUnit, ha, ha]
      exact (ω.2 n).symm
    refine ⟨W, Subtype.ext (funext fun n => ?_)⟩
    rw [toOmega_val, ← ha, eq_comm]
    exact (dUnit_eq_cls hre n _ W).2 ((X.der_unique n _ _ _ (hw n)).2 (hW n))

end PositivityTheory.HtPt.Twomega

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

theorem PositivityTheory.HtPt.Twomega.tower_omega : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L) [Module.Free O L] [Module.Finite O L] (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate) (hre : X.Realises G e τ), ∃ j : G.omega ≃ₗ[O] Module.Dual O L, (∀ (χ : G.dual.Tate) n, X.der n (e n (charElem χ n)).1 (j (dlog G χ))) ∧ ∀ (φ : La →+ La) (dφ : L →ₗ[O] L) (f : G ⟶ G), X.Acts φ dφ → (∀ n (g : G.A n) (a : La), (e n (f.app n g)).1 (lev p n a) = (e n g).1 (lev p n (φ a))) → ∀ w, j (omegaMap G G f w) = j w ∘ₗ dφ := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO La _ _ _ L _ _ X _ _ G e τ hre
  let k := LinearEquiv.ofBijective _ (PositivityTheory.HtPt.Twomega.toOmega_bijective hO hre)
  have hk : ∀ (ω : G.omega) n, ω.1 n = PositivityTheory.HtPt.Twomega.cls e n (k.symm ω) := fun ω n =>
    congrArg (fun x : G.omega => x.1 n) (k.apply_symm_apply ω).symm
  refine ⟨k.symm, fun χ n => ?_, fun φ dφ f hφ hf ω => ?_⟩
  · exact (PositivityTheory.HtPt.Twomega.dUnit_eq_cls hre n _ _).1 (hk (dlog G χ) n)
  · rw [LinearEquiv.symm_apply_eq]
    refine Subtype.ext (funext fun n => ?_)
    obtain ⟨a, ha⟩ := PositivityTheory.HtPt.Twomega.exists_der e n (k.symm ω)
    rw [omegaMap_val, hk ω n, ← (PositivityTheory.HtPt.Twomega.dUnit_eq_cls hre n a _).2 ha, PDiv.cotMap_d]
    exact (PositivityTheory.HtPt.Twomega.dUnit_eq_cls hre n _ _).2 ((hφ n _ _ (hf n a)).2 _ ha)
