import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingEveryOrdering
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.Graded
import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.LinkRing

noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct

def psPi (ι R : Type) [CommRing R] : (ι → PowerSeries R) →+* PowerSeries (ι → R) where
  toFun f := PowerSeries.mk fun k i => PowerSeries.coeff k (f i)
  map_one' := by
    ext k i
    simp only [PowerSeries.coeff_mk, Pi.one_apply, PowerSeries.coeff_one]
    split_ifs <;> rfl
  map_mul' f g := by
    ext k i
    simp only [PowerSeries.coeff_mk, Pi.mul_apply, PowerSeries.coeff_mul, Finset.sum_apply]
  map_zero' := by
    ext k i
    simp
  map_add' f g := by
    ext k i
    simp

@[simp] theorem coeff_psPi {ι R : Type} [CommRing R] (f : ι → PowerSeries R) (k : ℕ) (i : ι) :
    PowerSeries.coeff k (psPi ι R f) i = PowerSeries.coeff k (f i) := by
  simp [psPi]

theorem map_eval_psPi {ι R : Type} [CommRing R] (f : ι → PowerSeries R) (i : ι) :
    PowerSeries.map (Pi.evalRingHom (fun _ => R) i) (psPi ι R f) = f i := by
  ext k
  simp [PowerSeries.coeff_map]

section Roots

variable (LL : Type) [Field LL] (l : ℕ) [Fact l.Prime]

abbrev Rs (s : ℕ) : Type := ↥(primitiveRoots (l ^ (s + 1)) LL)

theorem pos_pow (s : ℕ) : 0 < l ^ (s + 1) := pow_pos (Fact.out : l.Prime).pos _

def powR (s : ℕ) (a : (ZMod (l ^ (s + 1)))ˣ) (ζ : Rs LL l s) : Rs LL l s :=
  ⟨(ζ : LL) ^ (a : ZMod (l ^ (s + 1))).val,
    LevelStatements.Link.pow_val_mem_primitiveRoots _ (pos_pow l s) _ a.isUnit ζ.2⟩

theorem rs_pow_N (s : ℕ) (ζ : Rs LL l s) : (ζ : LL) ^ (l ^ (s + 1)) = 1 :=
  ((mem_primitiveRoots (pos_pow l s)).1 ζ.2).pow_eq_one

theorem rs_pow_mod (s : ℕ) (ζ : Rs LL l s) (k : ℕ) :
    (ζ : LL) ^ (k % l ^ (s + 1)) = (ζ : LL) ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k (l ^ (s + 1)), pow_add, pow_mul, rs_pow_N, one_pow, mul_one]

theorem powR_powR (s : ℕ) (a b : (ZMod (l ^ (s + 1)))ˣ) (ζ : Rs LL l s) :
    powR LL l s a (powR LL l s b ζ) = powR LL l s (b * a) ζ := by
  apply Subtype.ext
  simp only [powR, Units.val_mul, ZMod.val_mul]
  rw [← pow_mul, rs_pow_mod]

theorem powR_one (s : ℕ) (ζ : Rs LL l s) : powR LL l s 1 ζ = ζ := by
  apply Subtype.ext
  simp only [powR, Units.val_one, ZMod.val_one_eq_one_mod]
  rw [rs_pow_mod, pow_one]

def precomp (s : ℕ) (a : (ZMod (l ^ (s + 1)))ˣ) :
    LevelStatements.Link.Ks LL l s ≃ₐ[LL] LevelStatements.Link.Ks LL l s where
  toFun f := fun ζ => f (powR LL l s a ζ)
  invFun f := fun ζ => f (powR LL l s a⁻¹ ζ)
  left_inv f := funext fun ζ => by
    simp only [powR_powR, inv_mul_cancel, powR_one]
  right_inv f := funext fun ζ => by
    simp only [powR_powR, mul_inv_cancel, powR_one]
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem precomp_apply (s : ℕ) (a : (ZMod (l ^ (s + 1)))ˣ) (f : LevelStatements.Link.Ks LL l s) (ζ : Rs LL l s) :
    precomp LL l s a f ζ = f (powR LL l s a ζ) := rfl

abbrev DeltaT : Type := {x : ℤ_[l]ˣ // x ^ (l - 1) = 1}

def redU (s : ℕ) (x : ℤ_[l]ˣ) : (ZMod (l ^ (s + 1)))ˣ :=
  Units.map (PadicInt.toZModPow (s + 1)).toMonoidHom x

def levOf (uZ : ℤ_[l]ˣ) (u : LLˣ) (aD : DeltaT l → LLˣ) (s : ℕ) :
    Level LL (LevelStatements.Link.Ks LL l s) (DeltaT l) where
  σ := precomp LL l s (redU l s uZ)
  u := u
  τ j := precomp LL l s (redU l s j.1)
  a := aD

end Roots

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

instance factP (PD : PeriodData G Qp K₀ K B BdR) : Fact PD.p.Prime := ⟨PD.hp⟩

variable {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

structure LevB (W : LocWach PD LL O v n) where
  levB : ∀ T : LocLat G Qp LL O, ZMod n → LL → ↥(W.N T) →+ (ℤ → T.V ⊗[Qp] B)
  mem : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
    levB T i ζ x k ∈ DcrisL PD T.ρ (W.emb i)
  supp : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)),
    ∃ m : ℤ, ∀ k < m, levB T i ζ x k = 0

variable {W : LocWach PD LL O v n}

abbrev KsW (W : LocWach PD LL O v n) (s : ℕ) : Type := LevelStatements.Link.Ks LL PD.p s

def rhoZ (W : LocWach PD LL O v n) (c : ZMod n) (ζ : LL) : PowerSeries O →ₐ[O] PowerSeries LL :=
  (W.lev c ζ).comp (AlgHom.pi fun _ => AlgHom.id O (PowerSeries O))

def rhoL (hR : Ring9 W) (c : ZMod n) (s : ℕ) : PowerSeries O →+* PowerSeries (KsW W s) :=
  (psPi (Rs LL PD.p s) LL).comp
    (RingHom.pi fun ζ => ((rhoZ W c ζ).comp (baseIdOf hR).ι).toRingHom)

theorem map_eval_rhoL (hR : Ring9 W) (c : ZMod n) (s : ℕ) (a : PowerSeries O) (ζ : Rs LL PD.p s) :
    PowerSeries.map (Pi.evalRingHom (fun _ => LL) ζ) (rhoL hR c s a) = rhoZ W c ζ ((baseIdOf hR).ι a) := by
  rw [rhoL, RingHom.comp_apply, map_eval_psPi]
  rfl

abbrev Dc (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n) : Type :=
  ↥(DcrisL PD T.ρ (W.emb c))

open Classical in

def toKsD (W : LocWach PD LL O v n) (s : ℕ) (D : Type) [AddCommGroup D] [Module LL D] :
    (Rs LL PD.p s → D) →ₗ[LL] KsW W s ⊗[LL] D :=
  (TensorProduct.comm LL D (Rs LL PD.p s → LL)).toLinearMap.comp
    (TensorProduct.piScalarRight LL LL D (Rs LL PD.p s)).symm.toLinearMap

def coefN (Lb : LevB W) (s : ℕ) (T : LocLat G Qp LL O) (c : ZMod n) (x : ↥(W.N T)) (k : ℤ) :
    KsW W s ⊗[LL] Dc W T c :=
  toKsD W s (Dc W T c) fun ζ => ⟨Lb.levB T c ζ x k, Lb.mem T c ζ x k⟩

theorem bdd_coefN (Lb : LevB W) (s : ℕ) (T : LocLat G Qp LL O) (c : ZMod n) (x : ↥(W.N T)) :
    BddBelow (Function.support (coefN Lb s T c x)) := by
  classical
  choose m hm using fun ζ : Rs LL PD.p s => Lb.supp T c ζ x
  refine ⟨-(∑ ζ, |m ζ|), fun k hk => ?_⟩
  by_contra hlt
  push Not at hlt
  apply hk
  have h0 : (fun ζ : Rs LL PD.p s => (⟨Lb.levB T c ζ x k, Lb.mem T c ζ x k⟩ : Dc W T c)) = 0 := by
    funext ζ
    apply Subtype.ext
    refine hm ζ k ?_
    have h1 := Finset.single_le_sum (f := fun ζ => |m ζ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ ζ)
    have h2 := neg_abs_le (m ζ)
    linarith
  simp only [coefN, h0, map_zero]

def expN (Lb : LevB W) (s : ℕ) (T : LocLat G Qp LL O) (c : ZMod n) (x : ↥(W.N T)) :
    Amb LL (KsW W s) (Dc W T c) :=
  HahnModule.of (KsW W s) (HahnSeries.ofSuppBddBelow (coefN Lb s T c x) (bdd_coefN Lb s T c x))

section Carrier

variable (hR : Ring9 W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O)

def levW (W : LocWach PD LL O v n) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) (s : ℕ) :
    Level LL (KsW W s) (DeltaT PD.p) :=
  levOf LL PD.p uZ (Units.map (algebraMap O LL).toMonoidHom (W.χΓ W.gam))
    (fun j => Units.map ((algebraMap O LL).comp ιZ).toMonoidHom j.1) s

def AmbM (_hR : Ring9 W) (T : LocLat G Qp LL O) (c : ZMod n) (s : ℕ) : Type :=
  Amb LL (KsW W s) (Dc W T c)

instance (T : LocLat G Qp LL O) (c : ZMod n) (s : ℕ) : AddCommGroup (AmbM hR T c s) :=
  inferInstanceAs (AddCommGroup (Amb LL (KsW W s) (Dc W T c)))

instance (T : LocLat G Qp LL O) (c : ZMod n) (s : ℕ) : Module (PowerSeries O) (AmbM hR T c s) :=
  Module.compHom (Amb LL (KsW W s) (Dc W T c))
    ((HahnSeries.ofPowerSeries ℤ (KsW W s)).comp (rhoL hR c s))

def toA (T : LocLat G Qp LL O) (c : ZMod n) (s : ℕ) : AmbM hR T c s →+ Amb LL (KsW W s) (Dc W T c) :=
  AddMonoidHom.id _

theorem toA_smul (T : LocLat G Qp LL O) (c : ZMod n) (s : ℕ) (a : PowerSeries O) (f : AmbM hR T c s) :
    toA hR T c s (a • f) = HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a) • toA hR T c s f := rfl

def DeltaRho (c : ZMod n) : Prop :=
  ∀ (s : ℕ) (j : DeltaT PD.p) (a : PowerSeries O),
    grdB ((levW W uZ ιZ s).τ j) ((levW W uZ ιZ s).a j)
      (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a)) =
      HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a)

def invSub (T : LocLat G Qp LL O) (c : ZMod n) (hΔ : DeltaRho hR uZ ιZ c) (s : ℕ) :
    Submodule (PowerSeries O) (AmbM hR T c s) where
  carrier := {f | (levW W uZ ιZ s).Inv (D := Dc W T c) (toA hR T c s f)}
  add_mem' := fun {f g} hf hg j => by
    simp only [Set.mem_ofPred_eq, map_add] at hf hg ⊢
    rw [hf j, hg j]
  zero_mem' := fun j => by
    simp only [map_zero]
  smul_mem' := fun a f hf j => by
    simp only [Set.mem_ofPred_eq] at hf ⊢
    rw [toA_smul, Level.δ, graded_semilinear_holds, hΔ s j a]
    exact congrArg _ (hf j)

abbrev LvT (T : LocLat G Qp LL O) (c : ZMod n) (hΔ : DeltaRho hR uZ ιZ c) (ell : ℕ) : Type :=
  ∀ s : Fin ell, ↥(invSub hR uZ ιZ T c hΔ s)

variable {hR uZ ιZ} {T : LocLat G Qp LL O} {c : ZMod n} {hΔ : DeltaRho hR uZ ιZ c} {ell : ℕ}

def prL (s : ℕ) : LvT hR uZ ιZ T c hΔ ell →+ Amb LL (KsW W s) (Dc W T c) where
  toFun e := if h : s < ell then toA hR T c s (e ⟨s, h⟩ : AmbM hR T c s) else 0
  map_zero' := by
    split_ifs <;> simp
  map_add' e e' := by
    split_ifs <;> simp

theorem prL_of_lt (s : ℕ) (h : s < ell) (e : LvT hR uZ ιZ T c hΔ ell) :
    prL s e = toA hR T c s (e ⟨s, h⟩ : AmbM hR T c s) := dif_pos h

theorem prL_of_ge (s : ℕ) (h : ¬ s < ell) (e : LvT hR uZ ιZ T c hΔ ell) : prL s e = 0 := dif_neg h

theorem prL_smul (s : ℕ) (a : PowerSeries O) (e : LvT hR uZ ιZ T c hΔ ell) :
    prL s (a • e) = HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a) • prL s e := by
  by_cases h : s < ell
  · rw [prL_of_lt s h, prL_of_lt s h]
    rfl
  · rw [prL_of_ge s h, prL_of_ge s h, smul_zero]

theorem prL_inj (e e' : LvT hR uZ ιZ T c hΔ ell) (h : ∀ s < ell, prL s e = prL s e') : e = e' := by
  funext s
  apply Subtype.ext
  have := h s s.2
  rw [prL_of_lt s s.2, prL_of_lt s s.2] at this
  exact this

theorem prL_inv (s : ℕ) (e : LvT hR uZ ιZ T c hΔ ell) :
    (levW W uZ ιZ s).Inv (D := Dc W T c) (prL s e) := by
  by_cases h : s < ell
  · rw [prL_of_lt s h]
    exact (e ⟨s, h⟩).2
  · rw [prL_of_ge s h]
    intro j
    exact map_zero _

end Carrier

section Maps

variable {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O} {T : LocLat G Qp LL O} {c : ZMod n}
  {hΔ : DeltaRho hR uZ ιZ c} {ell : ℕ}

theorem coefN_add (Lb : LevB W) (s : ℕ) (x y : ↥(W.N T)) :
    coefN Lb s T c (x + y) = coefN Lb s T c x + coefN Lb s T c y := by
  funext k
  simp only [coefN, Pi.add_apply]
  rw [← map_add]
  congr 1
  funext ζ
  apply Subtype.ext
  simp [map_add]

theorem expN_add (Lb : LevB W) (s : ℕ) (x y : ↥(W.N T)) :
    expN Lb s T c (x + y) = expN Lb s T c x + expN Lb s T c y := by
  have h : HahnSeries.ofSuppBddBelow (coefN Lb s T c (x + y)) (bdd_coefN Lb s T c (x + y)) =
      HahnSeries.ofSuppBddBelow (coefN Lb s T c x) (bdd_coefN Lb s T c x) +
        HahnSeries.ofSuppBddBelow (coefN Lb s T c y) (bdd_coefN Lb s T c y) := by
    ext k
    simp [HahnSeries.ofSuppBddBelow, coefN_add]
  simp only [expN, h]
  rfl

def ExpSemi (Lb : LevB W) (hR : Ring9 W) (T : LocLat G Qp LL O) (c : ZMod n) : Prop :=
  ∀ (s : ℕ) (a : PowerSeries O) (y : ↥(W.N T)) (hy : (baseIdOf hR).d a • (y : W.DD T) ∈ W.N T),
    expN Lb s T c ⟨_, hy⟩ = HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a) • expN Lb s T c y

variable (Lb : LevB W) (C : Coord W (baseIdOf hR) T)

def locF (κ : PowerSeries O) (s : ℕ) (x : C.V) (hx : x ∈ (latOf C).N c) :
    Amb LL (KsW W s) (Dc W T c) :=
  Ring.inverse (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s κ)) • expN Lb s T c ⟨C.t c x, hx⟩

def LocInv (c : ZMod n) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) (κ : PowerSeries O) : Prop :=
  ∀ (s : ℕ) (x : C.V) (hx : x ∈ (latOf C).N c),
    (levW W uZ ιZ s).Inv (D := Dc W T c) (locF Lb C κ s x hx)

theorem locF_congr (κ : PowerSeries O) (s : ℕ) {x y : C.V} (hx : x ∈ (latOf C).N c)
    (hy : y ∈ (latOf C).N c) (h : x = y) : locF Lb C κ s x hx = locF Lb C κ s y hy := by
  subst h
  rfl

def locM (hΔ : DeltaRho hR uZ ιZ c) (ell : ℕ) (Λ κ : PowerSeries O)
    (hκ : ∀ w ∈ (latOf C).W c ell Λ, κ • w ∈ (latOf C).N c) (hS : ExpSemi Lb hR T c)
    (hI : LocInv Lb C c uZ ιZ κ) :
    ↥((latOf C).W c ell Λ) →ₗ[PowerSeries O] LvT hR uZ ιZ T c hΔ ell where
  toFun w := fun s => ⟨locF Lb C κ s (κ • (w : C.V)) (hκ w w.2), hI s _ _⟩
  map_add' w w' := by
    funext s
    apply Subtype.ext
    change locF Lb C κ s (κ • ((w : C.V) + w')) _ =
      locF Lb C κ s (κ • (w : C.V)) _ + locF Lb C κ s (κ • (w' : C.V)) _
    have hxy : (⟨C.t c (κ • ((w : C.V) + w')), hκ (w + w') (w + w').2⟩ : ↥(W.N T)) =
        ⟨C.t c (κ • (w : C.V)), hκ w w.2⟩ + ⟨C.t c (κ • (w' : C.V)), hκ w' w'.2⟩ := by
      apply Subtype.ext
      simp [smul_add, C.t_add]
    simp only [locF]
    rw [hxy, expN_add, smul_add]
    rfl
  map_smul' a w := by
    funext s
    apply Subtype.ext
    change locF Lb C κ s (κ • (a • (w : C.V))) _ =
      HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a) • locF Lb C κ s (κ • (w : C.V)) _
    have hm : (baseIdOf hR).d a • C.t c (κ • (w : C.V)) ∈ W.N T := by
      rw [← C.t_smul, smul_comm]
      exact hκ (a • w) (a • w).2
    have hxy : (⟨C.t c (κ • (a • (w : C.V))), hκ (a • w) (a • w).2⟩ : ↥(W.N T)) =
        ⟨(baseIdOf hR).d a • C.t c (κ • (w : C.V)), hm⟩ := by
      apply Subtype.ext
      change C.t c (κ • (a • (w : C.V))) = _
      rw [smul_comm, C.t_smul]
    simp only [locF]
    rw [hxy, hS s a ⟨C.t c (κ • (w : C.V)), hκ w w.2⟩ hm, smul_comm]

def locLF {r : ℕ} (Λ : PowerSeries O) (lam : Fin r → Dc W T c) (s : ℕ) (y : Fin r → PowerSeries O) :
    Amb LL (KsW W s) (Dc W T c) :=
  Ring.inverse (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s Λ)) •
    ∑ k, HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s (y k)) • cstD (KsW W s) (lam k)

def LocLInv (hR : Ring9 W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) (T : LocLat G Qp LL O) (c : ZMod n)
    {r : ℕ} (Λ : PowerSeries O) (lam : Fin r → Dc W T c) : Prop :=
  ∀ (s : ℕ) (y : Fin r → PowerSeries O),
    (levW W uZ ιZ s).Inv (D := Dc W T c) (locLF (hR := hR) Λ lam s y)

def locLM (hΔ : DeltaRho hR uZ ιZ c) (ell : ℕ) {r : ℕ} (Λ : PowerSeries O) (lam : Fin r → Dc W T c)
    (hI : LocLInv hR uZ ιZ T c Λ lam) :
    (Fin r → PowerSeries O) →ₗ[PowerSeries O] LvT hR uZ ιZ T c hΔ ell where
  toFun y := fun s => ⟨locLF (hR := hR) Λ lam s y, hI s y⟩
  map_add' y y' := by
    funext s
    apply Subtype.ext
    change locLF (hR := hR) Λ lam s (y + y') = locLF (hR := hR) Λ lam s y + locLF (hR := hR) Λ lam s y'
    simp only [locLF, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib, smul_add]
  map_smul' a y := by
    funext s
    apply Subtype.ext
    change locLF (hR := hR) Λ lam s (a • y) =
      HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a) • locLF (hR := hR) Λ lam s y
    simp only [locLF, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, ← Finset.smul_sum]
    rw [smul_comm]

def FilD (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n) (s : ℕ) (u : ℤ) :
    Submodule LL (Dc W T c) :=
  (FilLev W T c s u).comap ((ιV PD (LL := LL) (V := T.V)).comp (DcrisL PD T.ρ (W.emb c)).subtype)

theorem tw_mono (m : ℤ) : Monotone (Tw (LL := LL) (D := Dc W T c) m) := by
  intro i j hij
  unfold Tw
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h1.trans hij) h2
  · exact bot_le
  · exact le_rfl

def NlS (hFil : ∀ s, Antitone (FilD W T c s)) (s : ℕ) :
    Submodule (PowerSeries O) (LvT hR uZ ιZ T c hΔ ell) where
  carrier := {e | prL s e ∈ Xi (KsW W s) (fun i => FilD W T c s (-i))}
  add_mem' := fun {e e'} he he' => by
    simp only [Set.mem_ofPred_eq, map_add] at he he' ⊢
    exact add_mem he he'
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact zero_mem _
  smul_mem' := fun a e he => by
    simp only [Set.mem_ofPred_eq] at he ⊢
    rw [prL_smul]
    exact xi_module_structure LL (KsW W s) (Dc W T c) _ (fun i j h => hFil s (neg_le_neg h)) _ _ he

def NbS (kind : ℕ → Kind) (b : ℕ → ℕ) (η : ℕ) (s : ℕ) :
    Submodule (PowerSeries O) (LvT hR uZ ιZ T c hΔ ell) where
  carrier := {e | prL s e ∈ Xi (KsW W s) (NbK (kind s) (b s) (UOf (kind s) (b s) η (FilD W T c s)))}
  add_mem' := fun {e e'} he he' => by
    simp only [Set.mem_ofPred_eq, map_add] at he he' ⊢
    exact add_mem he he'
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact zero_mem _
  smul_mem' := fun a e he => by
    simp only [Set.mem_ofPred_eq] at he ⊢
    rw [prL_smul]
    exact xi_module_structure LL (KsW W s) (Dc W T c) _ (Formalism.ExponentWindows.G.SlopeTestRemainingChoices.nbK_mono _ _ (by positivity) _) _ _ he

def FlS (Λ f' : PowerSeries O) (s : ℕ) : Submodule (PowerSeries O) (LvT hR uZ ιZ T c hΔ ell) where
  carrier := {e | ∃ x ∈ Xi (KsW W s) (Tw (LL := LL) (D := Dc W T c) 0),
    prL s (Λ • e) = HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s f') • x}
  add_mem' := fun {e e'} ⟨x, hx, he⟩ ⟨x', hx', he'⟩ =>
    ⟨x + x', add_mem hx hx', by rw [smul_add, map_add, he, he', smul_add]⟩
  zero_mem' := ⟨0, zero_mem _, by rw [smul_zero, map_zero, smul_zero]⟩
  smul_mem' := fun a e ⟨x, hx, he⟩ =>
    ⟨HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a) • x,
      xi_module_structure LL (KsW W s) (Dc W T c) _ (tw_mono 0) _ _ hx, by
        rw [smul_comm Λ a, prL_smul, he, smul_comm]⟩

def DcS (ell : ℕ) : AddSubgroup (LvT hR uZ ιZ T c hΔ ell) where
  carrier := {e | ∃ d : Dc W T c, ∀ s' < ell, prL s' e = cstD (KsW W s') d}
  add_mem' := fun {e e'} ⟨d, hd⟩ ⟨d', hd'⟩ => ⟨d + d', fun s' hs' => by
    rw [map_add, hd s' hs', hd' s' hs']
    simp [cstD, TensorProduct.tmul_add]⟩
  zero_mem' := ⟨0, fun s' _ => by simp [cstD]⟩
  neg_mem' := fun {e} ⟨d, hd⟩ => ⟨-d, fun s' hs' => by
    rw [map_neg, hd s' hs']
    simp [cstD, TensorProduct.tmul_neg]
    rfl⟩

end Maps

section Assembly

variable {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O} {T : LocLat G Qp LL O} {c : ZMod n}

structure LvHyp (Lb : LevB W) (hR : Ring9 W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O)
    (C : Coord W (baseIdOf hR) T) (c : ZMod n) (ell : ℕ) (Λ κ : PowerSeries O) {r : ℕ}
    (lam : Fin r → Dc W T c) : Prop where

  delta : DeltaRho hR uZ ιZ c

  gamInv : ∀ (s : ℕ) (f : Amb LL (KsW W s) (Dc W T c)), (levW W uZ ιZ s).Inv f →
    (levW W uZ ιZ s).Inv ((levW W uZ ιZ s).γ f)

  gamRho : ∀ (s : ℕ) (a : PowerSeries O),
    grdB (levW W uZ ιZ s).σ (levW W uZ ιZ s).u (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a)) =
      HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s ((baseIdOf hR).Bs.γ a))

  kap : ∀ w ∈ (latOf C).W c ell Λ, κ • w ∈ (latOf C).N c

  expSemi : ExpSemi Lb hR T c

  locInv : LocInv Lb C c uZ ιZ κ

  loclInv : LocLInv hR uZ ιZ T c Λ lam

  filAnti : ∀ s, Antitone (FilD W T c s)

  rhoC : ∀ (s : ℕ) (a : O), rhoL hR c s (PowerSeries.C a) =
    PowerSeries.C (algebraMap LL (KsW W s) (algebraMap O LL a))

variable {Lb : LevB W} {C : Coord W (baseIdOf hR) T} {ell : ℕ} {Λ κ : PowerSeries O} {r : ℕ}
  {lam : Fin r → Dc W T c}

def gEL (H : LvHyp Lb hR uZ ιZ C c ell Λ κ lam) :
    LvT hR uZ ιZ T c H.delta ell →+ LvT hR uZ ιZ T c H.delta ell where
  toFun e := fun s => ⟨(levW W uZ ιZ s).γ (toA hR T c s (e s : AmbM hR T c s)),
    H.gamInv s _ (e s).2⟩
  map_zero' := by
    funext s
    apply Subtype.ext
    exact map_zero _
  map_add' e e' := by
    funext s
    apply Subtype.ext
    exact map_add _ _ _

theorem prL_gEL (H : LvHyp Lb hR uZ ιZ C c ell Λ κ lam) (s' : ℕ) (hs' : s' < ell)
    (e : LvT hR uZ ιZ T c H.delta ell) :
    prL s' (gEL H e) = (levW W uZ ιZ s').γ (prL s' e) := by
  rw [prL_of_lt s' hs', prL_of_lt s' hs']
  rfl

def cstL (hΔ : DeltaRho hR uZ ιZ c) (ell : ℕ) (d : Dc W T c) : LvT hR uZ ιZ T c hΔ ell :=
  fun s => ⟨cstD (KsW W s) d, fun j => Formalism.ExponentWindows.G.SlopeTestRemainingChoices.grd_cst _ _ d⟩

theorem prL_cstL {hΔ : DeltaRho hR uZ ιZ c} (s' : ℕ) (hs' : s' < ell) (d : Dc W T c) :
    prL s' (cstL hΔ ell d) = cstD (KsW W s') d := by
  rw [prL_of_lt s' hs']
  rfl

def lvData (H : LvHyp Lb hR uZ ιZ C c ell Λ κ lam) (f' : PowerSeries O) (kind : ℕ → Kind)
    (b : ℕ → ℕ) (η : ℕ) : E.LevelData (latOf C) c ell Λ r where
  Lv := LvT hR uZ ιZ T c H.delta ell
  gE := fun _ => gEL H
  gE_semi := fun _ a e => by
    funext s
    apply Subtype.ext
    change (levW W uZ ιZ s).γ (HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s a) •
      toA hR T c s (e s : AmbM hR T c s)) =
      HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s ((baseIdOf hR).Bs.γ a)) •
        (levW W uZ ιZ s).γ (toA hR T c s (e s : AmbM hR T c s))
    rw [Level.γ, graded_semilinear_holds, H.gamRho s a]
  loc := fun _ => locM Lb C H.delta ell Λ κ H.kap H.expSemi H.locInv
  locL := fun _ => locLM H.delta ell Λ lam H.loclInv
  Nl := NlS H.filAnti
  Nb := NbS kind b η
  Fl := FlS Λ f'
  Dc := fun _ => DcS ell

def lvModel (H : LvHyp Lb hR uZ ιZ C c ell Λ κ lam) (f' : PowerSeries O) (kind : ℕ → Kind)
    (b : ℕ → ℕ) (η : ℕ) :
    LevelModel (lvData H f' kind b η) LL (KsW W) (DeltaT PD.p) (Dc W T c) where
  lev := levW W uZ ιZ
  ρ := rhoL hR c
  ρ_C := H.rhoC
  pr := prL
  pr_smul := prL_smul
  pr_γ := fun _ _ s' hs' e => prL_gEL H s' hs' e
  pr_inv := fun s _ e => prL_inv s e
  pr_inj := prL_inj
  Fil := FilD W T c
  kind := kind
  b := b
  η := η
  mem_Nl := fun _ _ _ => Iff.rfl
  mem_Nb := fun _ _ _ => Iff.rfl
  mem_Dc := fun _ _ _ => Iff.rfl
  const := fun d => ⟨cstL H.delta ell d, fun s' hs' => prL_cstL s' hs' d⟩

def UL (lam : Fin r → Dc W T c) (kind : ℕ → Kind) (b : ℕ → ℕ) (η : ℕ) (s : ℕ) :
    Submodule O (Fin r → O) where
  carrier := {v | ∑ k, algebraMap O LL (v k) • lam k ∈ UOf (kind s) (b s) η (FilD W T c s)}
  add_mem' := fun {v w} hv hw => by
    simp only [Set.mem_ofPred_eq, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib] at hv hw ⊢
    exact add_mem hv hw
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, Pi.zero_apply, map_zero, zero_smul, Finset.sum_const_zero]
    exact zero_mem _
  smul_mem' := fun a v hv => by
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul] at hv ⊢
    rw [← Finset.smul_sum]
    exact Submodule.smul_mem _ _ hv

end Assembly

section MapDefs

def ambMap {Ks D₁ D₂ : Type} [CommRing Ks] [Algebra LL Ks] [AddCommGroup D₁] [Module LL D₁]
    [AddCommGroup D₂] [Module LL D₂] (g : Ks ⊗[LL] D₁ →ₗ[Ks] Ks ⊗[LL] D₂) :
    Amb LL Ks D₁ →+ Amb LL Ks D₂ where
  toFun f := HahnModule.of Ks (((HahnModule.of Ks).symm f).map g.toAddMonoidHom)
  map_zero' := by
    apply (HahnModule.of Ks).symm.injective
    ext k
    simp
  map_add' f f' := by
    apply (HahnModule.of Ks).symm.injective
    ext k
    simp

variable {T₁ T₂ : LocLat G Qp LL O}

def MemD (W : LocWach PD LL O v n) (F : LatHom T₁.L T₂.L) (c : ZMod n) : Prop :=
  ∀ x ∈ DcrisL PD T₁.ρ (W.emb c),
    AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B) x ∈ DcrisL PD T₂.ρ (W.emb c)

def dmapOf {F : LatHom T₁.L T₂.L} {c : ZMod n} (h : MemD W F c) : Dc W T₁ c →ₗ[LL] Dc W T₂ c :=
  ((AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B)).domRestrict
    (DcrisL PD T₁.ρ (W.emb c))).codRestrict (DcrisL PD T₂.ρ (W.emb c)) (fun x => h x x.2)

def ambF {F : LatHom T₁.L T₂.L} {c : ZMod n} (h : MemD W F c) (s : ℕ) :
    Amb LL (KsW W s) (Dc W T₁ c) →+ Amb LL (KsW W s) (Dc W T₂ c) :=
  ambMap ((dmapOf h).baseChange (KsW W s))

variable {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O} {c : ZMod n}

structure MapHyp (hR : Ring9 W) (uZ : ℤ_[PD.p]ˣ) (ιZ : ℤ_[PD.p] →+* O) (F : LatHom T₁.L T₂.L)
    (c : ZMod n) : Prop where

  memD : MemD W F c

  smul : ∀ (s : ℕ) (x : HahnSeries ℤ (KsW W s)) (f : Amb LL (KsW W s) (Dc W T₁ c)),
    ambF memD s (x • f) = x • ambF memD s f

  inv : ∀ (s : ℕ) (f : Amb LL (KsW W s) (Dc W T₁ c)), (levW W uZ ιZ s).Inv f →
    (levW W uZ ιZ s).Inv (ambF memD s f)

def prEOf {F : LatHom T₁.L T₂.L} (M : MapHyp hR uZ ιZ F c) {hΔ₁ : DeltaRho hR uZ ιZ c}
    {hΔ₂ : DeltaRho hR uZ ιZ c} (ell : ℕ) :
    LvT hR uZ ιZ T₁ c hΔ₁ ell →ₗ[PowerSeries O] LvT hR uZ ιZ T₂ c hΔ₂ ell where
  toFun e := fun s => ⟨ambF M.memD s (toA hR T₁ c s (e s : AmbM hR T₁ c s)), M.inv s _ (e s).2⟩
  map_add' e e' := by
    funext s
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' a e := by
    funext s
    apply Subtype.ext
    exact M.smul s _ _

theorem prL_prEOf {F : LatHom T₁.L T₂.L} (M : MapHyp hR uZ ιZ F c) {hΔ₁ : DeltaRho hR uZ ιZ c}
    {hΔ₂ : DeltaRho hR uZ ιZ c} {ell : ℕ} (s : ℕ) (hs : s < ell)
    (e : LvT hR uZ ιZ T₁ c hΔ₁ ell) :
    prL s (prEOf M (hΔ₂ := hΔ₂) ell e) = ambF M.memD s (prL s e) := by
  rw [prL_of_lt s hs, prL_of_lt s hs]
  rfl

end MapDefs

section abelian₂

variable {hR : Ring9 W} {T : LocLat G Qp LL O}

open Classical in

def lamOf (C : Coord W (baseIdOf hR) T) (c : ZMod n) (ell : ℕ) {r : ℕ} (e : Fin r → C.V) (k : Fin r) :
    Dc W T c :=
  if h : C.t (c - (ell : ZMod n)) (e k) ∈ W.N T then
    (if h' : ((φVB PD (LL := LL) (V := T.V)) ^ ell) (W.cmp T ⟨_, h⟩) ∈ DcrisL PD T.ρ (W.emb c) then
      ⟨_, h'⟩ else 0)
  else 0

end abelian₂

end Formalism.MainNotions.N.Ln03
