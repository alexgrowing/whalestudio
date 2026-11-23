import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.SolCnt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.FinTwLc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.DdSumZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

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

section red
variable {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n)

private theorem dg_smul {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g : ℕ} (c : A) (y : DD X g) :
    c • y = ⟨algebraMap A X c * y.a, fun j => algebraMap A X c * y.ep j, fun j => algebraMap A X c * y.ep' j,
      algebraMap A X c * y.eta⟩ := by
  have : c • y = DD.C (algebraMap A X c) * y := rfl
  rw [this]
  ext <;> simp

private theorem dg_q (m : ℕ) (a b : x.A) :
    Ideal.Quotient.mk (Ideal.span {x.t ^ m}) a = Ideal.Quotient.mk _ b ↔
      ∀ d < m, PowerSeries.coeff d a = PowerSeries.coeff d b := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
  simp only [map_sub, sub_eq_zero]

private theorem dg_red (g m : ℕ) (a b : DD x.A g) : x.redD g m a = x.redD g m b ↔
    Ideal.Quotient.mk (Ideal.span {x.t ^ m}) a.a = Ideal.Quotient.mk _ b.a ∧
    (∀ j, Ideal.Quotient.mk (Ideal.span {x.t ^ m}) (a.ep j) = Ideal.Quotient.mk _ (b.ep j)) ∧
    (∀ j, Ideal.Quotient.mk (Ideal.span {x.t ^ m}) (a.ep' j) = Ideal.Quotient.mk _ (b.ep' j)) ∧
    Ideal.Quotient.mk (Ideal.span {x.t ^ m}) a.eta = Ideal.Quotient.mk _ b.eta := by
  rw [DD.ext_iff, funext_iff, funext_iff]
  rfl

private theorem dg_qsep {a : x.A}
    (e : ∀ m, Ideal.Quotient.mk (Ideal.span {x.t ^ m}) a = Ideal.Quotient.mk _ 0) : a = 0 :=
  PowerSeries.ext fun d => (dg_q x (d + 1) a 0).1 (e _) d (Nat.lt_succ_self d)

private theorem dg_sep {g : ℕ} {a : DD x.A g} (e : ∀ m, x.redD g m a = 0) : a = 0 := by
  have e' : ∀ m, x.redD g m a = x.redD g m 0 := fun m => by rw [e, map_zero]
  simp only [dg_red] at e'
  ext1
  · exact dg_qsep x fun m => (e' m).1
  · exact funext fun j => dg_qsep x fun m => (e' m).2.1 j
  · exact funext fun j => dg_qsep x fun m => (e' m).2.2.1 j
  · exact dg_qsep x fun m => (e' m).2.2.2

private theorem dg_surj (g m : ℕ) : Function.Surjective (x.redD g m) := by
  rintro ⟨a, ep, ep', eta⟩
  have s := Ideal.Quotient.mk_surjective (I := Ideal.span {x.t ^ m})
  obtain ⟨a, rfl⟩ := s a
  obtain ⟨eta, rfl⟩ := s eta
  choose e he using fun j => s (ep j)
  choose e' he' using fun j => s (ep' j)
  exact ⟨⟨a, e, e', eta⟩, DD.ext rfl (funext he) (funext he') rfl⟩

private theorem dg_ker (g m : ℕ) (a : DD x.A g) : x.redD g m a = 0 ↔ ∃ p, x.t ^ m • p = a := by
  constructor
  · intro e
    rw [← map_zero (x.redD g m), dg_red] at e
    simp only [Ideal.Quotient.eq, Ideal.mem_span_singleton, DD.zero_a, DD.zero_ep, DD.zero_ep', DD.zero_eta,
      sub_zero] at e
    obtain ⟨⟨a', ha⟩, h2, h3, ⟨eta', heta⟩⟩ := e
    choose e he using h2
    choose e' he' using h3
    refine ⟨⟨a', e, e', eta'⟩, ?_⟩
    rw [dg_smul]
    exact DD.ext ha.symm (funext fun j => (he j).symm) (funext fun j => (he' j).symm) heta.symm
  · rintro ⟨p, rfl⟩
    have h0 : algebraMap x.A (x.Am m) (x.t ^ m) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    rw [map_smul, dg_smul, h0]
    ext <;> simp

private theorem dg_tf (g : ℕ) (a : DD x.A g) (h : x.t • a = 0) : a = 0 := by
  rw [dg_smul, DD.ext_iff, funext_iff, funext_iff] at h
  simpa [DD.ext_iff, funext_iff] using h

private theorem dg_qcomp (u : ℕ → x.A) (h : ∀ m n, m ≤ n →
    Ideal.Quotient.mk (Ideal.span {x.t ^ m}) (u m) = Ideal.Quotient.mk _ (u n)) :
    ∃ L, ∀ m, Ideal.Quotient.mk (Ideal.span {x.t ^ m}) (u m) = Ideal.Quotient.mk _ L := by
  refine ⟨PowerSeries.mk fun d => PowerSeries.coeff d (u (d + 1)), fun m => (dg_q x _ _ _).2 fun d hd => ?_⟩
  rw [PowerSeries.coeff_mk]
  exact ((dg_q x _ _ _).1 (h (d + 1) m hd) d (Nat.lt_succ_self d)).symm

private theorem dg_comp (g : ℕ) (u : ℕ → DD x.A g) (h : ∀ m n, m ≤ n → x.redD g m (u m) = x.redD g m (u n)) :
    ∃ L, ∀ m, x.redD g m (u m) = x.redD g m L := by
  simp only [dg_red] at h ⊢
  obtain ⟨a, ha⟩ := dg_qcomp x _ fun m n e => (h m n e).1
  choose b hb using fun j => dg_qcomp x _ fun m n e => (h m n e).2.1 j
  choose c hc using fun j => dg_qcomp x _ fun m n e => (h m n e).2.2.1 j
  obtain ⟨d, hd⟩ := dg_qcomp x _ fun m n e => (h m n e).2.2.2
  exact ⟨⟨a, b, c, d⟩, fun m => ⟨ha m, fun j => hb j m, fun j => hc j m, hd m⟩⟩

private theorem dg_lc {Γ R : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) R) :
    IsLocallyConstant f ↔ ∀ i j, IsLocallyConstant fun g => f g i j := by
  refine ⟨fun h i j => h.comp fun Z => Z i j, fun h => ?_⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g0
  have : ∀ᶠ g in nhds g0, ∀ i j, f g i j = f g0 i j :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (h i j).eventually_eq g0
  filter_upwards [this] with g hg
  exact Matrix.ext hg

private theorem dg_cont {Γ : Type} [TopologicalSpace Γ] {g : ℕ} (f : Γ → DD x.A g)
    (h : ∀ m, IsLocallyConstant fun s => x.redD g m (f s)) :
    AdicCont (Ideal.span {algebraMap x.A (DD x.A g) x.t}) f := by
  intro m
  have h1 := h m
  rw [IsLocallyConstant.iff_eventually_eq] at h1 ⊢
  refine fun s => (h1 s).mono fun s' e => ?_
  rw [← sub_eq_zero, ← map_sub, dg_ker] at e
  obtain ⟨p, hp⟩ := e
  rw [Ideal.Quotient.eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← map_pow, ← hp, Algebra.smul_def]
  exact dvd_mul_right _ _

variable {x} (k : Kap x)

private theorem dg_ρ1 (m : ℕ) (g : F.G₀) : (x.redD k.g m).mapMatrix (k.ρ1 x.A g) = k.ρ1 (x.Am m) g := by
  have a1 : ∀ Z : Fin k.g → Matrix (Fin n) (Fin n) x.A,
      (x.redD k.g m).mapMatrix (DD.epM fun j => (Z j).map (algebraMap x.A x.A)) =
      DD.epM fun j => (Z j).map (algebraMap x.A (x.Am m)) := fun Z => by
    ext a b <;> simp [DD.epM]
  have a2 : ∀ Z : Matrix (Fin n) (Fin n) x.A, (x.redD k.g m).mapMatrix (Z.map (algebraMap x.A (DD x.A k.g))) =
      Z.map (algebraMap x.A (DD (x.Am m) k.g)) := fun Z => by
    ext1 a b
    exact (x.redD k.g m).commutes _
  simp only [Kap.ρ1, NP.ρX, map_mul, map_add, map_one, a1, a2]

private theorem dg_eps (m : ℕ) (g : F.Γ) (Z : Matrix (Fin n) (Fin n) (DD x.A k.g)) :
    (x.redD k.g m).mapMatrix (epsD k x.A g • Z) = epsD k (x.Am m) g • (x.redD k.g m).mapMatrix Z := by
  simp only [epsD, algebraMap_smul, map_smul]

private def dgCut {X : Type} [CommRing X] {g : ℕ} (a : ℕ) (Z : Matrix (Fin n) (Fin n) (DD X g)) :
    Matrix (Fin n) (Fin n) (DD X g) :=
  Matrix.of fun i j => if ((i : ℕ) < a ↔ (j : ℕ) < a) then ⟨(Z i j).a, (Z i j).ep, (Z i j).ep', 0⟩
    else ⟨(Z i j).a, (Z i j).ep, 0, (Z i j).eta⟩

private theorem dgCut_iff {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g : ℕ} (a : ℕ)
    (Z : Matrix (Fin n) (Fin n) (DD X g)) : dgCut a Z = 0 ↔ Z ∈ pairedDualFirstOrderDualMatrixSpace n A X g a := by
  rw [← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  by_cases h : ((i : ℕ) < a ↔ (j : ℕ) < a)
  · simp only [dgCut, Matrix.of_apply, if_pos h]
    simp [h, ddPart, DD.ext_iff, funext_iff]
  · simp only [dgCut, Matrix.of_apply, if_neg h]
    simp [h, ddPart, DD.ext_iff, funext_iff]

variable (X : Type) [CommRing X] [Algebra x.A X] {q : ℕ} (sg : Fin q → F.G₀)

private noncomputable def dgPhi (z : F.G₀ → Matrix (Fin n) (Fin n) (DD X k.g)) :
    F.G₀ ⊕ (F.G₀ × F.G₀) ⊕ F.G₀ ⊕ Fin q → Matrix (Fin n) (Fin n) (DD X k.g)
  | .inl g => dgCut x.a (z g)
  | .inr (.inl p) => z (p.1 * p.2) - (z p.1 + epsD k X p.1 • (k.ρ1 X p.1 * z p.2 * k.ρ1 X p.1⁻¹))
  | .inr (.inr (.inl g)) => z (F.conj g) - -(epsD k X F.c • (z g)ᵀ)
  | .inr (.inr (.inr j)) => Matrix.of fun _ _ => DD.C (ell k X (sg j) z)

private theorem dgPhi_iff (z : F.G₀ → Matrix (Fin n) (Fin n) (DD X k.g)) :
    (∀ i, dgPhi k X sg z i = 0) ↔ (∀ g, z g ∈ pairedDualFirstOrderDualMatrixSpace n x.A X k.g x.a) ∧
      (∀ g h, z (g * h) = z g + epsD k X g • (k.ρ1 X g * z h * k.ρ1 X g⁻¹)) ∧
      (∀ g, z (F.conj g) = -(epsD k X F.c • (z g)ᵀ)) ∧ ∀ j, ell k X (sg j) z = 0 := by
  simp only [Sum.forall, Prod.forall, dgPhi, sub_eq_zero, dgCut_iff (A := x.A)]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun j => ⟨fun h => ?_, fun h => ?_⟩)))
  · have i : Fin n := ⟨0, lt_of_lt_of_le x.a_pos x.a_le⟩
    exact congrArg DD.a (congrFun (congrFun h i) i)
  · rw [h, map_zero]; rfl

private noncomputable def dgL : (F.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g)) →ₗ[x.A]
    (F.G₀ ⊕ (F.G₀ × F.G₀) ⊕ F.G₀ ⊕ Fin q → Matrix (Fin n) (Fin n) (DD x.A k.g)) where
  toFun := dgPhi k x.A sg
  map_add' z w := by
    funext i
    rcases i with g | p | g | j
    · ext1 a b
      simp only [dgPhi, dgCut, Pi.add_apply, Matrix.add_apply, Matrix.of_apply]
      split_ifs <;> ext <;> simp
    · simp only [dgPhi, Pi.add_apply, Matrix.mul_add, Matrix.add_mul, smul_add]; abel
    · simp only [dgPhi, Pi.add_apply, Matrix.transpose_add, smul_add]; abel
    · ext1 a b
      simp [dgPhi, ell, Matrix.add_mul]
  map_smul' c z := by
    funext i
    rcases i with g | p | g | j
    · ext1 a b
      simp only [dgPhi, dgCut, Pi.smul_apply, Matrix.smul_apply, Matrix.of_apply, RingHom.id_apply, dg_smul]
      split_ifs <;> ext <;> simp
    · simp only [dgPhi, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_sub, RingHom.id_apply,
        smul_comm c (epsD k x.A _)]
    · simp only [dgPhi, Pi.smul_apply, Matrix.transpose_smul, smul_sub, smul_neg, RingHom.id_apply,
        smul_comm c (epsD k x.A _)]
    · ext1 a b
      simp only [dgPhi, ell, Pi.smul_apply, Matrix.smul_mul, Matrix.trace_smul, Matrix.smul_apply, Matrix.of_apply,
        RingHom.id_apply, dg_smul]
      ext <;> simp

private theorem dgPhi_nat (m : ℕ) (z : F.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g)) (i) :
    (x.redD k.g m).mapMatrix (dgPhi k x.A sg z i) =
      dgPhi k (x.Am m) sg (fun g => (x.redD k.g m).mapMatrix (z g)) i := by
  rcases i with g | p | g | j
  · ext1 a b
    simp only [dgPhi, dgCut, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> ext <;> simp
  · simp only [dgPhi, map_sub, map_add, dg_eps, map_mul, dg_ρ1]
  · simp only [dgPhi, map_sub, map_neg, dg_eps]
    rfl
  · have : ell k (x.Am m) (sg j) (fun g => (x.redD k.g m).mapMatrix (z g)) =
        Ideal.Quotient.mkₐ x.A _ (ell k x.A (sg j) z) := by
      rw [ell, ← dg_ρ1, ← map_mul, AlgHom.mapMatrix_apply, ← AddMonoidHom.map_trace (x.redD k.g m)]
      rfl
    ext1 a b
    simp only [dgPhi]
    rw [this]
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    ext <;> simp

private def dgB : Submodule x.A (F.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g)) where
  carrier := TwB k x.A
  add_mem' := by
    rintro _ _ ⟨Y, a1, a2, rfl⟩ ⟨Y', b1, b2, rfl⟩
    refine ⟨Y + Y', add_mem a1 b1, ?_, funext fun g => ?_⟩
    · rw [Matrix.transpose_add, smul_add, neg_add, a2, b2]
    · simp only [Pi.add_apply, Matrix.mul_add, Matrix.add_mul, smul_add]; abel
  zero_mem' := ⟨0, zero_mem _, by simp, funext fun g => by simp⟩
  smul_mem' := by
    rintro c _ ⟨Y, a1, a2, rfl⟩
    refine ⟨c • Y, Submodule.smul_mem _ c a1, ?_, funext fun g => ?_⟩
    · rw [Matrix.transpose_smul, smul_comm, ← smul_neg, a2]
    · simp only [Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_comm c (epsD k x.A _)]

end red

theorem UpperTheory.V.Pa.exists_ncard_annihilated_cocycles_le_coboundaries_mul :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (q : ℕ) (sg : Fin q → G0.G₀), PhiCond G0.Γ l → (∀ j, sg j ∈ G0.frame.G') → Detects k (Set.range sg) → ∃ C : ℕ, ∀ m, {z | z ∈ TwZ k (x.Am m) ∧ ∀ j, ell k (x.Am m) (sg j) z = 0}.ncard ≤ (TwB k (x.Am m)).ncard * Nat.card x.K ^ C := by
  intro l _ L G0 n x k q sg hΦ hsg hD
  let χ : G0.Γ →* x.A :=
    ((algebraMap ℤ_[l] x.A : ℤ_[l] →+* x.A) : ℤ_[l] →* x.A).comp ((Units.coeHom ℤ_[l]).comp G0.ε)
  have hok : AdOk G0.frame (fun g => k.ρ1 x.A g) (fun g => epsD k x.A g) (pairedDualFirstOrderDualMatrixSpace n x.A x.A k.g x.a) :=
    (ok1 l L G0 G0 (Glob.Hom.refl G0) n x k x.A χ).2.1
  obtain ⟨rep, r1, r2⟩ := adEx l G0.frame _ _ n _ _ _ hok
  have eK : IsLocalRing.ResidueField x.A ≃ x.K := (PowerSeries.residueFieldOfPowerSeries (k := x.K)).toEquiv
  haveI : Finite (IsLocalRing.ResidueField x.A) := Finite.of_equiv _ eK.symm
  rw [← Nat.card_congr eK]
  refine dg_abs x.A _ G0.G₀ _ x.t (fun m => Matrix (Fin n) (Fin n) (DD (x.Am m) k.g))
    (fun m => (x.redD k.g m).mapMatrix.toLinearMap) (dgL k sg) (dgB k)
    (fun m => {z | z ∈ TwZ k (x.Am m) ∧ ∀ j, ell k (x.Am m) (sg j) z = 0}) (fun m => TwB k (x.Am m))
    PowerSeries.X_irreducible inferInstance (fun m Z => ?_) (fun m Z => ?_)
    (fun Z h => Matrix.ext fun i j => dg_tf x _ _ (congrFun (congrFun h i) j))
    (fun Z h => Matrix.ext fun i j => dg_sep x fun m => congrFun (congrFun (h m) i) j) (fun u h => ?_)
    (fun m f => ?_) ((finTw l L G0 n x k 1 hΦ).subset fun z hz => hz.1) (fun m => ?_) ?_ (fun f hf h0 => ?_)
  · choose Y hY using fun i j => dg_surj x k.g m (Z i j)
    exact ⟨Matrix.of Y, Matrix.ext hY⟩
  · constructor
    · intro h
      choose Y hY using fun i j => (dg_ker x k.g m (Z i j)).1 (congrFun (congrFun h i) j)
      exact ⟨Matrix.of Y, Matrix.ext hY⟩
    · rintro ⟨Y, rfl⟩
      exact Matrix.ext fun i j => (dg_ker x k.g m _).2 ⟨Y i j, rfl⟩
  · choose Y hY using fun i j => dg_comp x k.g (fun m => u m i j) fun a b e => congrFun (congrFun (h a b e) i) j
    exact ⟨Matrix.of Y, fun m => Matrix.ext fun i j => hY i j m⟩
  · obtain ⟨-, -, -, -, -, -, ht, -⟩ := finAm l G0.frame n x m k.g
    have e : (∀ i, (x.redD k.g m).mapMatrix (dgPhi k x.A sg f i) = 0) ↔ _ :=
      (forall_congr' fun i => by rw [dgPhi_nat]).trans
        (dgPhi_iff k (x.Am m) sg fun g => (x.redD k.g m).mapMatrix (f g))
    refine ⟨fun ⟨⟨a1, a2, a3, a4⟩, a5⟩ => ⟨(dg_lc _).2 fun i j => (adicLC _ _ _ m _ ht).1 (a2 i j),
      e.2 ⟨a1, a3, a4, a5⟩⟩, fun ⟨a1, a2⟩ => ?_⟩
    obtain ⟨b1, b2, b3, b4⟩ := e.1 a2
    exact ⟨⟨b1, fun i j => (adicLC _ _ _ m _ ht).2 ((dg_lc _).1 a1 i j), b2, b3⟩, b4⟩
  · haveI := (finAm l G0.frame n x m k.g).2.2.1
    haveI : Finite (Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) :=
      inferInstanceAs (Finite (Fin n → Fin n → DD (x.Am m) k.g))
    refine (Set.finite_range fun (Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) (g : G0.frame.G₀) =>
      epsD k (x.Am m) g • (k.ρ1 (x.Am m) g * Y * k.ρ1 (x.Am m) g⁻¹) - Y).subset ?_
    rintro _ ⟨Y, -, -, rfl⟩
    exact ⟨Y, rfl⟩
  · rintro _ ⟨Y, a1, a2, rfl⟩
    refine ⟨funext ((dgPhi_iff k x.A sg _).2 ?_), fun m => ⟨(x.redD k.g m).mapMatrix Y, ?_, ?_, funext fun g => ?_⟩⟩
    · obtain ⟨y, rfl⟩ : ∃ y : pairedDualFirstOrderDualMatrixSpace n x.A x.A k.g x.a, y.1 = Y := ⟨⟨Y, a1⟩, rfl⟩
      have hc : rep G0.c y = y := Subtype.ext ((r2 y).trans a2)
      have hc' : rep G0.c⁻¹ y = y := by
        conv_lhs => rw [← hc, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
      have e : ∀ g : G0.frame.G₀, epsD k x.A g • (k.ρ1 x.A g * y.1 * k.ρ1 x.A g⁻¹) - y.1 = (rep g y - y).1 :=
        fun g => by rw [Submodule.coe_sub, r1]
      refine ⟨fun g => by rw [e]; exact Subtype.property _, fun g h => ?_, fun g => ?_, fun j => ?_⟩
      · rw [e, e, e]
        refine Eq.trans ?_ (congrArg _ (r1 g _))
        rw [← Submodule.coe_add, Subgroup.coe_mul, map_mul, map_sub, Module.End.mul_apply, sub_add_sub_cancel']
      · rw [e, e]
        refine Eq.trans ?_ (r2 _)
        have : ((G0.frame.conj g : G0.frame.G₀) : G0.Γ) = G0.c * g * G0.c⁻¹ := rfl
        rw [this, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hc', map_sub, hc]
      · have h1 : G0.ε (sg j) = 1 := hsg j
        have h2 : epsD k x.A (sg j : G0.frame.G₀) = 1 := by
          change algebraMap x.A _ (algebraMap ℤ_[l] x.A (G0.ε (sg j) : ℤ_[l])) = 1
          rw [h1, Units.val_one, map_one, map_one]
        have h3 : k.ρ1 x.A (sg j)⁻¹ * k.ρ1 x.A (sg j) = 1 := by
          rw [← (rho1 l _ n x k x.A).2.1, inv_mul_cancel, (rho1 l _ n x k x.A).1]
        simp only [ell]
        rw [h2, one_smul, Matrix.sub_mul, Matrix.mul_assoc, h3, Matrix.mul_one, Matrix.trace_sub,
          Matrix.trace_mul_comm, sub_self, DD.zero_eta]
    · have := dgPhi_nat k sg m (fun _ => Y) (.inl 1)
      simp only [dgPhi] at this
      rw [(dgCut_iff (A := x.A) _ _).2 a1, map_zero] at this
      exact (dgCut_iff _ _).1 this.symm
    · have := congrArg (x.redD k.g m).mapMatrix a2
      rw [map_neg, dg_eps] at this
      exact this
    · change (x.redD k.g m).mapMatrix (_ - _) = _
      simp only [map_sub, dg_eps, map_mul, dg_ρ1]
  · obtain ⟨b1, b2, b3, b4⟩ := (dgPhi_iff k x.A sg f).1 (congrFun h0)
    refine hD f ⟨b1, fun i j => dg_cont x _ fun m => (dg_lc _).1 (hf m) i j, b2, b3⟩ ?_
    rintro _ ⟨j, rfl⟩
    exact b4 j
