import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.FinTwO
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.OmFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.SolCnt

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem dg_mem {A C : Type} [CommRing A] [AddCommGroup C] [Module A C] (a : A) (x : C) :
    x ∈ (Ideal.span {a} • ⊤ : Submodule A C) ↔ ∃ c, a • c = x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp

private theorem dg_equiv {A C D : Type} [CommRing A] [AddCommGroup C] [Module A C] [AddCommGroup D] [Module A D]
    (R : C →ₗ[A] D) (T S : Submodule A C) (h : LinearMap.ker R = T) : Nonempty (S.map T.mkQ ≃ (R '' S : Set D)) := by
  have hi : Function.Injective (T.liftQ R h.ge) := by
    rw [← LinearMap.ker_eq_bot]; exact Submodule.ker_liftQ_eq_bot _ _ _ h.le
  have e := Submodule.equivMapOfInjective _ hi (S.map T.mkQ)
  rw [← Submodule.map_comp, Submodule.liftQ_mkQ] at e
  exact ⟨e.toEquiv⟩

private theorem dg_abs (A P G ι : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Finite (IsLocalRing.ResidueField A)] [AddCommGroup P] [Module A P] [TopologicalSpace G] (t : A)
    (Pm : ℕ → Type) [∀ m, AddCommGroup (Pm m)] [∀ m, Module A (Pm m)] (red : ∀ m, P →ₗ[A] Pm m)
    (Φ : (G → P) →ₗ[A] (ι → P)) (B : Submodule A (G → P)) (Z Bm : ∀ m, Set (G → Pm m))
    (ht : Irreducible t) (hA : IsAdicComplete (Ideal.span {t}) A)
    (hsurj : ∀ m, Function.Surjective (red m)) (hker : ∀ m p, red m p = 0 ↔ ∃ p', t ^ m • p' = p)
    (htf : ∀ p : P, t • p = 0 → p = 0) (hsep : ∀ p, (∀ m, red m p = 0) → p = 0)
    (hcomp : ∀ u : ℕ → P, (∀ m n, m ≤ n → red m (u m) = red m (u n)) → ∃ L, ∀ m, red m (u m) = red m L)
    (hZ : ∀ m (f : G → P), (red m ∘ f) ∈ Z m ↔ IsLocallyConstant (red m ∘ f) ∧ ∀ i, red m (Φ f i) = 0)
    (hZ1 : (Z 1).Finite) (hBm : ∀ m, (Bm m).Finite)
    (hB : ∀ b ∈ B, Φ b = 0 ∧ ∀ m, red m ∘ b ∈ Bm m)
    (hdet : ∀ f : G → P, (∀ m, IsLocallyConstant (red m ∘ f)) → Φ f = 0 → ∃ s : ℕ, t ^ s • f ∈ B) :
    ∃ e : ℕ, ∀ m, (Z m).ncard ≤ (Bm m).ncard * Nat.card (IsLocalRing.ResidueField A) ^ e := by
  have htf' : ∀ (n : ℕ) (y : P), t ^ n • y = 0 → y = 0 := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih => exact fun y hy => htf y (ih _ (by rw [smul_smul, ← pow_succ, hy]))
  let C : Submodule A (G → P) :=
    { carrier := {f | ∀ m, IsLocallyConstant (red m ∘ f)}
      add_mem' := fun {a b} ha hb m => by
        have : red m ∘ (a + b) = red m ∘ a + red m ∘ b := by funext g; simp
        rw [this]; exact (ha m).add (hb m)
      zero_mem' := fun m => by
        have : red m ∘ (0 : G → P) = fun _ => 0 := by funext g; simp
        rw [this]; exact IsLocallyConstant.const _
      smul_mem' := fun c a ha m => by
        have : red m ∘ (c • a) = (fun y => c • y) ∘ (red m ∘ a) := by funext g; simp
        rw [this]; exact (ha m).comp _ }
  have mC' : ∀ m (y : ι → P), y ∈ (Ideal.span {t ^ m} • ⊤ : Submodule A (ι → P)) ↔ ∀ i, red m (y i) = 0 := by
    intro m y
    rw [dg_mem]
    simp only [hker]
    exact ⟨fun ⟨c, hc⟩ i => ⟨c i, congrFun hc i⟩, fun h => by choose c hc using h; exact ⟨c, funext hc⟩⟩
  have mC : ∀ m (f : C), f ∈ (Ideal.span {t ^ m} • ⊤ : Submodule A C) ↔ ∀ g, red m (f.1 g) = 0 := by
    intro m f
    rw [dg_mem]
    simp only [hker]
    refine ⟨fun ⟨c, hc⟩ i => ⟨c.1 i, congrFun (congrArg Subtype.val hc) i⟩, fun h => ?_⟩
    choose c hc using h
    refine ⟨⟨c, fun N => ?_⟩, Subtype.ext (funext hc)⟩
    have h1 := f.2 (m + N)
    rw [IsLocallyConstant.iff_eventually_eq] at h1 ⊢
    refine fun g => (h1 g).mono fun g' e => ?_
    simp only [Function.comp] at e ⊢
    rw [← sub_eq_zero, ← map_sub, hker] at e ⊢
    obtain ⟨p, hp⟩ := e
    refine ⟨p, sub_eq_zero.1 (htf' m _ ?_)⟩
    rw [smul_sub, smul_sub, hc, hc, smul_smul, ← pow_add, hp, sub_self]
  let R : ∀ m, C →ₗ[A] (G → Pm m) := fun m => ((red m).compLeft G).comp C.subtype
  have hR : ∀ m, LinearMap.ker (R m) = (Ideal.span {t ^ m} • ⊤ : Submodule A C) := fun m => by
    ext f
    rw [mC, LinearMap.mem_ker, funext_iff]
    rfl
  have hS : ∀ m, R m '' ((Ideal.span {t ^ m} • ⊤ : Submodule A (ι → P)).comap (Φ.comp C.subtype) : Submodule A C)
      = Z m := fun m => by
    ext h
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact (hZ m f.1).2 ⟨f.2 m, (mC' m _).1 hf⟩
    · intro hh
      obtain ⟨s, hs⟩ := (hsurj m).hasRightInverse
      have e : red m ∘ (s ∘ h) = h := funext fun g => hs _
      have h2 := (hZ m (s ∘ h)).1 (by rw [e]; exact hh)
      rw [e] at h2
      exact ⟨⟨s ∘ h, fun N => h2.1.comp (red N ∘ s)⟩, (mC' m _).2 h2.2, e⟩
  have hH : IsHausdorff (Ideal.span {t}) C := ⟨fun f hf => Subtype.ext (funext fun g => hsep _ fun m => by
    have := hf m
    rw [SModEq.sub_mem, Ideal.span_singleton_pow, sub_zero, mC] at this
    exact this g)⟩
  have hH' : IsHausdorff (Ideal.span {t}) (ι → P) := ⟨fun f hf => funext fun g => hsep _ fun m => by
    have := hf m
    rw [SModEq.sub_mem, Ideal.span_singleton_pow, sub_zero, mC'] at this
    exact this g⟩
  have hP : IsPrecomplete (Ideal.span {t}) C := ⟨fun u hu => by
    have h1 : ∀ g, ∃ L, ∀ m, red m ((u m).1 g) = red m L := fun g => hcomp _ fun m n hmn => by
      have := hu hmn
      rw [SModEq.sub_mem, Ideal.span_singleton_pow, mC] at this
      rw [← sub_eq_zero, ← map_sub]
      exact this g
    choose L hL using h1
    refine ⟨⟨L, fun m => ?_⟩, fun m => ?_⟩
    · have : red m ∘ L = red m ∘ (u m).1 := funext fun g => (hL g m).symm
      rw [this]; exact (u m).2 m
    · rw [SModEq.sub_mem, Ideal.span_singleton_pow, mC]
      intro g
      exact (map_sub _ _ _).trans (sub_eq_zero.2 (hL g m))⟩
  obtain ⟨-, e, he⟩ := solCnt A C (ι → P) t (Φ.comp C.subtype) (B.comap C.subtype) ht
    (fun y hy => Subtype.ext (funext fun g => htf _ (congrFun (congrArg Subtype.val hy) g)))
    (fun y hy => funext fun g => htf _ (congrFun hy g)) hA {} hH'
    (by
      obtain ⟨e⟩ := dg_equiv (R 1) _
        ((Ideal.span {t ^ 1} • ⊤ : Submodule A (ι → P)).comap (Φ.comp C.subtype)) (hR 1)
      rw [hS, pow_one] at e
      have := hZ1.to_subtype
      exact Finite.of_equiv _ e.symm)
    (fun b hb => (hB _ hb).1) (fun z hz => hdet z.1 z.2 hz)
  refine ⟨e, fun m => ?_⟩
  obtain ⟨e1⟩ := dg_equiv (R m) _
    ((Ideal.span {t ^ m} • ⊤ : Submodule A (ι → P)).comap (Φ.comp C.subtype)) (hR m)
  obtain ⟨e2⟩ := dg_equiv (R m) _ (B.comap C.subtype) (hR m)
  have h3 := (he m).2
  rw [Nat.card_congr e1, Nat.card_congr e2, hS, Nat.card_coe_set_eq, Nat.card_coe_set_eq] at h3
  refine h3.trans (Nat.mul_le_mul_right _ (Set.ncard_le_ncard ?_ (hBm m)))
  rintro _ ⟨b, hb, rfl⟩
  exact (hB _ hb).2 m

private theorem dg_lc {Γ R : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) R) :
    IsLocallyConstant f ↔ ∀ i j, IsLocallyConstant fun g => f g i j := by
  refine ⟨fun h i j => h.comp fun Z => Z i j, fun h => ?_⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g0
  have : ∀ᶠ g in nhds g0, ∀ i j, f g i j = f g0 i j :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (h i j).eventually_eq g0
  filter_upwards [this] with g hg
  exact Matrix.ext hg

section phi
variable {G : Type} [Group G] {n q : ℕ}

private def dgPhi {R : Type} [CommRing R] (ρ : G → Matrix (Fin n) (Fin n) R) (e : G → R) (P : Matrix (Fin n) (Fin n) R)
    (cj : G → G) (sg : Fin q → G) (z : G → Matrix (Fin n) (Fin n) R) :
    (G × G) ⊕ G ⊕ (Fin q × ℕ) → Matrix (Fin n) (Fin n) R
  | .inl p => z (p.1 * p.2) - (z p.1 + e p.1 • (ρ p.1 * z p.2 * ρ p.1⁻¹))
  | .inr (.inl g) => P * z (cj g) - (z g)ᵀ * P
  | .inr (.inr j) => Matrix.of fun _ _ => (z (sg j.1) * ρ (sg j.1) ^ j.2).trace

private theorem dgPhi_iff {R : Type} [CommRing R] (ρ : G → Matrix (Fin n) (Fin n) R) (e : G → R)
    (P : Matrix (Fin n) (Fin n) R) (cj : G → G) (sg : Fin q → G) (z : G → Matrix (Fin n) (Fin n) R) :
    (∀ i, dgPhi ρ e P cj sg z i = 0) ↔ (∀ g h, z (g * h) = z g + e g • (ρ g * z h * ρ g⁻¹)) ∧
      (∀ g, P * z (cj g) = (z g)ᵀ * P) ∧ ∀ j (k : ℕ), (z (sg j) * ρ (sg j) ^ k).trace = 0 := by
  simp only [Sum.forall, Prod.forall, dgPhi, sub_eq_zero]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall₂_congr fun j k => ⟨fun h => ?_, fun h => ?_⟩))
  · rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨i⟩⟩
    · simp [Matrix.trace]
    · exact congrFun (congrFun h i) i
  · rw [h]; rfl

private def dgL {R : Type} [CommRing R] (ρ : G → Matrix (Fin n) (Fin n) R) (e : G → R) (P : Matrix (Fin n) (Fin n) R)
    (cj : G → G) (sg : Fin q → G) : (G → Matrix (Fin n) (Fin n) R) →ₗ[R]
    ((G × G) ⊕ G ⊕ (Fin q × ℕ) → Matrix (Fin n) (Fin n) R) where
  toFun := dgPhi ρ e P cj sg
  map_add' z w := by
    funext i
    rcases i with p | g | j
    · simp only [dgPhi, Pi.add_apply, Matrix.mul_add, Matrix.add_mul, smul_add]; abel
    · simp only [dgPhi, Pi.add_apply, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]; abel
    · ext1 a b
      simp [dgPhi, Matrix.add_mul]
  map_smul' c z := by
    funext i
    rcases i with p | g | j
    · simp only [dgPhi, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_sub, RingHom.id_apply,
        smul_comm c (e _)]
    · simp only [dgPhi, Pi.smul_apply, Matrix.transpose_smul, smul_sub, Matrix.mul_smul, Matrix.smul_mul,
        RingHom.id_apply]
    · ext1 a b
      simp [dgPhi]

private theorem dg_smul {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (a : R) (Z : Matrix (Fin n) (Fin n) R) :
    φ.mapMatrix (a • Z) = φ a • φ.mapMatrix Z := by
  ext i j
  simp

private theorem dg_tr {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (Z : Matrix (Fin n) (Fin n) R) :
    φ.mapMatrix Zᵀ = (φ.mapMatrix Z)ᵀ := rfl

private theorem dgPhi_nat {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (ρ : G → Matrix (Fin n) (Fin n) R)
    (e : G → R) (P : Matrix (Fin n) (Fin n) R) (cj : G → G) (sg : Fin q → G) (z : G → Matrix (Fin n) (Fin n) R) (i) :
    φ.mapMatrix (dgPhi ρ e P cj sg z i) =
      dgPhi (fun g => φ.mapMatrix (ρ g)) (fun g => φ (e g)) (φ.mapMatrix P) cj sg (fun g => φ.mapMatrix (z g)) i := by
  rcases i with p | g | j
  · simp only [dgPhi, map_sub, map_add, dg_smul, map_mul]
  · simp only [dgPhi, map_sub, map_mul, dg_tr]
  · ext1 a b
    simp only [dgPhi]
    rw [← map_pow, ← map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace φ]
    rfl

private def dgB {R : Type} [CommRing R] (ρ : G → Matrix (Fin n) (Fin n) R) (e : G → R)
    (P : Matrix (Fin n) (Fin n) R) : Submodule R (G → Matrix (Fin n) (Fin n) R) where
  carrier := {z | ∃ Y, P * Y = Yᵀ * P ∧ z = fun g => e g • (ρ g * Y * ρ g⁻¹) - Y}
  add_mem' := by
    rintro _ _ ⟨Y, a2, rfl⟩ ⟨Y', b2, rfl⟩
    refine ⟨Y + Y', ?_, funext fun g => ?_⟩
    · rw [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, a2, b2]
    · simp only [Pi.add_apply, Matrix.mul_add, Matrix.add_mul, smul_add]; abel
  zero_mem' := ⟨0, by simp, funext fun g => by simp⟩
  smul_mem' := by
    rintro c _ ⟨Y, a2, rfl⟩
    refine ⟨c • Y, ?_, funext fun g => ?_⟩
    · rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, a2]
    · simp only [Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_comm c (e _)]

end phi

theorem UpperTheory.V.Th.ncard_traceZero_twisted_cocycles_le_coboundaries_mul :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (q : ℕ) (sg : Fin q → G0.G₀), PhiCond G0.Γ l → DetO y (Set.range sg) → ∃ C : ℕ, ∀ m, {z | z ∈ Tw y m ∧ ∀ j (k : ℕ), (z (sg j) * y.ρ0 m (sg j) ^ k).trace = 0}.ncard ≤ (TwB y m).ncard * Nat.card (ResidueField O) ^ C := by
  intro l _ L G0 O _ _ _ hO _ n y q sg hΦ hD
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hm : maximalIdeal O = Ideal.span {t} := ht.maximalIdeal_eq
  haveI : Finite (ResidueField O) := hO.finite
  have hA : IsAdicComplete (maximalIdeal O) O := hO.complete
  have hk : ∀ (m : ℕ) (a : O), Ideal.Quotient.mk (maximalIdeal O ^ m) a = 0 ↔ ∃ p, t ^ m • p = a := fun m a => by
    rw [Ideal.Quotient.eq_zero_iff_mem, hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨fun ⟨p, hp⟩ => ⟨p, hp.symm⟩, fun ⟨p, hp⟩ => ⟨p, hp.symm⟩⟩
  have hq : ∀ (m : ℕ) (a b : O), a ≡ b [SMOD (maximalIdeal O ^ m • ⊤ : Submodule O O)] ↔
      Ideal.Quotient.mk (maximalIdeal O ^ m) a = Ideal.Quotient.mk (maximalIdeal O ^ m) b := fun m a b => by
    rw [SModEq.sub_mem, Ideal.Quotient.eq, smul_eq_mul, Ideal.mul_top]
  let ρ : G0.G₀ → Matrix (Fin n) (Fin n) O := fun g => mat y.ρ g
  let e : G0.G₀ → O := fun g => algebraMap ℤ_[l] O (G0.ε g : ℤ_[l])
  let Φ := dgL ρ e y.P G0.frame.conj sg
  refine dg_abs O _ G0.G₀ _ t (fun m => Mm O n m)
    (fun m => (Ideal.Quotient.mkₐ O (maximalIdeal O ^ m)).mapMatrix.toLinearMap) Φ
    (dgB ρ e y.P ⊓ LinearMap.ker Φ)
    (fun m => {z | z ∈ Tw y m ∧ ∀ j (k : ℕ), (z (sg j) * y.ρ0 m (sg j) ^ k).trace = 0}) (fun m => TwB y m)
    ht (hm ▸ hA) (fun m Z => ?_) (fun m Z => ?_)
    (fun Z h => (smul_eq_zero.1 h).resolve_left ht.ne_zero)
    (fun Z h => Matrix.ext fun i j => hA.toIsHausdorff.haus _ fun m =>
      (hq m _ _).2 (congrFun (congrFun (h m) i) j)) (fun u h => ?_)
    (fun m f => ?_) ((finTwO l L G0 O n y 1 hΦ).subset fun z hz => hz.1) (fun m => ?_) ?_ (fun f hf h0 => ?_)
  · choose Y hY using fun i j => Ideal.Quotient.mk_surjective (I := maximalIdeal O ^ m) (Z i j)
    exact ⟨Matrix.of Y, Matrix.ext hY⟩
  · constructor
    · intro h
      choose Y hY using fun i j => (hk m (Z i j)).1 (congrFun (congrFun h i) j)
      exact ⟨Matrix.of Y, Matrix.ext hY⟩
    · rintro ⟨Y, rfl⟩
      exact Matrix.ext fun i j => (hk m _).2 ⟨Y i j, rfl⟩
  · choose Y hY using fun i j => hA.toIsPrecomplete.prec (f := fun m => u m i j)
      fun {a b} hab => (hq _ _ _).2 (congrFun (congrFun (h a b hab) i) j)
    exact ⟨Matrix.of Y, fun m => Matrix.ext fun i j => (hq _ _ _).1 (hY i j m)⟩
  · have e1 : (∀ i, (Ideal.Quotient.mk (maximalIdeal O ^ m)).mapMatrix (dgPhi ρ e y.P G0.frame.conj sg f i) = 0) ↔ _ :=
      (forall_congr' fun i => by rw [dgPhi_nat]).trans (dgPhi_iff _ _ _ _ sg _)
    refine ⟨fun ⟨⟨a1, a2, a3⟩, a4⟩ => ⟨a1, e1.2 ⟨a2, a3, a4⟩⟩, fun ⟨a1, a2⟩ => ?_⟩
    obtain ⟨b1, b2, b3⟩ := e1.1 a2
    exact ⟨⟨a1, b1, b2⟩, b3⟩
  · haveI := ((omFacts l O).2 m).1
    haveI : Finite (Mm O n m) := inferInstanceAs (Finite (Fin n → Fin n → Om O m))
    refine (Set.finite_range fun (Y : Mm O n m) (g : G0.G₀) =>
      epsm O G0 m g • (y.ρ0 m g * Y * y.ρ0 m g⁻¹) - Y).subset ?_
    rintro _ ⟨Y, -, rfl⟩
    exact ⟨Y, rfl⟩
  · rintro _ ⟨⟨Y, a2, rfl⟩, h0⟩
    refine ⟨h0, fun m => ⟨(Ideal.Quotient.mk (maximalIdeal O ^ m)).mapMatrix Y, ?_, funext fun g => ?_⟩⟩
    · have := congrArg (Ideal.Quotient.mk (maximalIdeal O ^ m)).mapMatrix a2
      rw [map_mul, map_mul] at this
      exact this
    · change (Ideal.Quotient.mk (maximalIdeal O ^ m)).mapMatrix (_ - _) = _
      rw [map_sub, dg_smul, map_mul, map_mul]
      rfl
  · obtain ⟨b1, b2, b3⟩ := (dgPhi_iff ρ e y.P G0.frame.conj sg f).1 (congrFun h0)
    obtain ⟨a, Y, ha, h1, h2⟩ := hD f (fun i j m => (dg_lc _).1 (hf m) i j) b1 b2
      (by rintro _ ⟨j, rfl⟩ k; exact b3 j k)
    obtain ⟨s, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha ht
    refine ⟨s, ?_, ?_⟩
    · rw [← hu, mul_comm, mul_smul]
      exact Submodule.smul_mem _ _ ⟨Y, h1, funext h2⟩
    · exact Submodule.smul_mem _ _ (LinearMap.mem_ker.2 h0)
