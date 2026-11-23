import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsPrimeToPLat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LKGeo

variable {p : ℕ} [Fact p.Prime]

abbrev VQ (D : Datum p) : Type := ℚ ⊗[ℤ] D.La

def actQ (D : Datum p) (b : D.O) : Module.End ℚ (VQ D) :=
  (DistribMulAction.toLinearMap ℤ D.La b).baseChange ℚ

def actOn {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V] (rep : C →ₐ[ℚ] Module.End ℚ V)
    (R : Type) [CommRing R] [Algebra ℚ R] : R ⊗[ℚ] C →ₐ[R] Module.End R (R ⊗[ℚ] V) :=
  Algebra.TensorProduct.lift (Algebra.ofId R _) ((Module.End.baseChangeHom ℚ R V).comp rep)
    (fun x _ => Algebra.commute_algebraMap_left x _)

structure Link (D : Datum p) (G : HTGroup p) where

  e : D.F ≃+* G.F
  n_eq : G.n = D.n

  rep : G.C →ₐ[ℚ] Module.End ℚ (VQ D)
  rep_inj : Function.Injective rep
  rep_range : ∀ A : Module.End ℚ (VQ D), (∃ x, rep x = A) ↔ ∀ b, A * actQ D b = actQ D b * A
  rep_F : ∀ c : 𝓞 D.F, rep (algebraMap G.F G.C (e c)) = actQ D (algebraMap (𝓞 D.F) D.O c)
  adj : ∀ x v w, D.EF.baseChange ℚ (rep x v) w = D.EF.baseChange ℚ v (rep (sh G x) w)

  ρp : ℤ_[p]
  ρp_eq : ∃ h : e D.ω ∈ G.Kq, G.u ⟨e D.ω, h⟩ = (ρp : ℚ_[p])

  s : Fin D.a → (G.F →+* AlgebraicClosure ℚ)
  s_C : ∀ i x, G.iotaC (s i (e x)) = D.tau i x

  w : Fin D.a → Fin G.m
  s_P : ∀ i x, G.iotaP (s i x) = G.emb (w i) x
  sig : ∀ v, sigPosH (G.gram_herm v) = 1 ↔ ∃ i, v = InfinitePlace.mk (G.iotaC.comp (s i))
  orient : ∃ J : ℝ ⊗[ℚ] G.C, J * J = -1 ∧ (starT G.star ℝ J).unop = -J ∧
    (∀ x, x ≠ 0 → 0 < (D.EF.baseChange ℚ).baseChange ℝ (actOn rep ℝ J x) x) ∧
    ∀ v : InfinitePlace G.F,
      ((if v.embedding (e D.ω) = D.ρc then -Complex.I else Complex.I) • (G.gram v * G.psiR v J)).PosDef

def HasDivPlace (G : HTGroup p) : Prop :=
  ∃ w : HeightOneSpectrum (𝓞 G.F), (p : 𝓞 G.F) ∉ w.asIdeal ∧
    ∀ x : w.adicCompletion G.F ⊗[G.F] G.C, x ≠ 0 → IsUnit x

def RegAf (G : HTGroup p) (ga : G.GAf) : Prop :=
  ∃ v : AwayP p, ∀ x y : v.1.adicCompletion ℚ ⊗[ℚ] G.C,
    Commute x ((ubcMap (AfP.eval v) ga).1.1 : v.1.adicCompletion ℚ ⊗[ℚ] G.C) →
    Commute y ((ubcMap (AfP.eval v) ga).1.1 : v.1.adicCompletion ℚ ⊗[ℚ] G.C) → Commute x y

def IsIntAf (a : AfP p) : Prop := ∀ v : AwayP p, AfP.eval v a ∈ v.1.adicCompletionIntegers ℚ

def LaHat (D : Datum p) : AddSubgroup (AfP p ⊗[ℚ] VQ D) :=
  AddSubgroup.closure {z | ∃ (a : AfP p) (x : D.La), IsIntAf a ∧ z = a ⊗ₜ ((1 : ℚ) ⊗ₜ x)}

def inAf (D : Datum p) (x : D.La) : AfP p ⊗[ℚ] VQ D := (1 : AfP p) ⊗ₜ ((1 : ℚ) ⊗ₜ x)

def mulKQ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) : KQ p K r →ₐ[ℚ_[p]] PadicAlgCl p :=
  Algebra.TensorProduct.lift K.val (Qr p r).val (fun _ _ => Commute.all _ _)

namespace Link

variable {D : Datum p} {G : HTGroup p} (L : Link D G)

def actG : G.GAf →* Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) :=
  ((actOn L.rep (AfP p)).toRingHom.toMonoidHom.comp (Units.coeHom _)).comp
    ((MonoidHom.fst _ _).comp (UPts G.star (AfP p)).subtype)

def CongOne (N : ℕ) (g : G.GAf) : Prop := ∀ v ∈ LaHat D, ∃ w ∈ LaHat D, L.actG g v = v + N • w

theorem CongOne.mul {N : ℕ} {g h : G.GAf} (hg : L.CongOne N g) (hh : L.CongOne N h) : L.CongOne N (g * h) := by
  intro v hv
  obtain ⟨w, hw, e1⟩ := hh v hv
  obtain ⟨w', hw', e2⟩ := hg (v + N • w) (add_mem hv (nsmul_mem hw N))
  refine ⟨w + w', add_mem hw hw', ?_⟩
  rw [map_mul, Module.End.mul_apply, e1, e2, smul_add, add_assoc]

def KN (N : ℕ) : Subgroup G.GAf where
  carrier := {g | L.CongOne N g ∧ L.CongOne N g⁻¹}
  one_mem' := by
    have h : L.CongOne N 1 := fun v _ => ⟨0, zero_mem _, by simp⟩
    exact ⟨h, by simpa using h⟩
  mul_mem' := fun hg hh => ⟨CongOne.mul L hg.1 hh.1, by rw [_root_.mul_inv_rev]; exact CongOne.mul L hh.2 hg.2⟩
  inv_mem' := fun hg => ⟨hg.2, by simpa using hg.1⟩

def MuSupp (r : ℕ) (δ : Gr G r) : Prop :=
  GlobalTheory.LKLoc.KotInv p (Q0 p) 1 r δ.1 (-1) ∧
  (∀ w, (∀ i j, ((δ.2 w)⁻¹).val i j ∈ intKQ p (G.Fw w) r) ∧
    ‖Algebra.norm ℚ_[p] (δ.2 w).val.det‖ = (p : ℝ) ^ (r * Nat.card {i // L.w i = w})) ∧
  ∀ i, 1 < ‖mulKQ (G.Fw (L.w i)) r ((sigKQ p (G.Fw (L.w i)) r)^[r - 1] (δ.2 (L.w i)).val.det)‖

def GoodSel (sel : Polynomial G.F → ℂ) : Prop :=
  IsSel G sel ∧ ∀ (i : Fin D.a) (P : Polynomial G.F), P.Monic → P.natDegree = G.n →
    (∃ mu, P.eval₂ (L.s i) mu = 0 ∧ 1 < ‖G.iotaP mu‖) →
    ∃ mu, P.eval₂ (L.s i) mu = 0 ∧ 1 < ‖G.iotaP mu‖ ∧
      sel P = if (InfinitePlace.mk (G.iotaC.comp (L.s i))).embedding = G.iotaC.comp (L.s i) then G.iotaC mu
        else (starRingEnd ℂ) (G.iotaC mu)

end Link

section Points

variable {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {k : Type} [Field k] {β : R →+* k} {N N' : ℕ}

def av (o : Obj b N (spMap β)) : AbVar k :=
  haveI : ConnectedSpace (Sp k) := GlobalTheory.AbelianDim.connectedSpace_spec_of_isLocalRing k
  { X := o.A
    ab := o.ab
    dim := (GlobalTheory.AbelianDim.exists_relDim_of_connected o.A o.ab).choose
    smooth := (GlobalTheory.AbelianDim.exists_relDim_of_connected o.A o.ab).choose_spec }

def actEnd (o : Obj b N (spMap β)) (c : D.O) : End (av o) :=
  @AbVar.Hom.mk k _ (av o) (av o) (o.act.act c) (o.act.hom c)

abbrev TIso (o : Obj b N (spMap β)) : Type :=
  TateIsoO D k (Over.mk (𝟙 (Sp k)) ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z))

def Induces (o : Obj b N (spMap β)) (I : TIso o) : Prop := ∀ y, toUnit _ ≫ o.eta y = I.ev N y

def IsoObj (o o' : Obj b N (spMap β)) : Prop := Nonempty (ObjMap o o' (𝟙 _))

def Pts (b : Base D R) (β : R →+* k) (N : ℕ) : Type 1 := Quot (IsoObj (b := b) (β := β) (N := N))

variable {G : HTGroup p} (L : Link D G)

def Acts {o : Obj b N (spMap β)} {o' : Obj b N' (spMap β)} (I : TIso o) (I' : TIso o') (ψ : av o ⟶ av o') (m : ℤ)
    (g : G.GAf) : Prop :=
  ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x y : D.La,
    I.ev n x ≫ (show o.A ⟶ o'.A from ψ.hom) = I'.ev n y ↔
      ∃ w ∈ LaHat D, m • L.actG g (inAf D x) = inAf D y + n • w

def ActsQ {o : Obj b N (spMap β)} (I : TIso o) (π : End0 (av o)) (g : G.GAf) : Prop :=
  ∀ (m : ℤ) (ψ : End (av o)), m • π = toEnd0 _ ψ → Acts L I I ψ m g

def IsGamma (o : Obj b N (spMap β)) (π : End0 (av o)) (g : G.GAf) : Prop :=
  ∃ I : TIso o, Induces o I ∧ ActsQ L I π g

def Transl (o : Obj b N (spMap β)) (o' : Obj b N' (spMap β)) (g : G.GAf) : Prop :=
  ∃ (I : TIso o) (I' : TIso o') (ψ : av o ⟶ av o') (ψ' : av o' ⟶ av o) (m d : ℕ), Induces o I ∧ Induces o' I' ∧
    m.Coprime p ∧ d.Coprime p ∧ ψ ≫ ψ' = d • 𝟙 _ ∧ ψ' ≫ ψ = d • 𝟙 _ ∧ Acts L I I' ψ m g

def Classifies (M : Model b N) (x : Sp k ⟶ M.X) (o : Obj b N (spMap β)) : Prop :=
  x ≫ M.s = spMap β ∧ Nonempty (ObjMap o M.univ x)

def IsHecke (β : R →+* k) (M' : Model b N') (M : Model b N) (q : M'.X ⟶ M.X) (g : G.GAf) : Prop :=
  q ≫ M.s = M'.s ∧ ∀ (y : Sp k ⟶ M'.X) (o' : Obj b N' (spMap β)) (o : Obj b N (spMap β)),
    Classifies M' y o' → Classifies M (y ≫ q) o → Transl L o' o g

variable [CharP k p] [PerfectRing k p]

def Compat (b : Base D R) (β : R →+* k) (red : (Obar p).toSubring →+* k) : Prop :=
  WittVector.constantCoeff (GlobalTheory.IsogParam.zpW p k L.ρp) = β b.ρ ∧
    ∀ (i : Fin D.a) (c : 𝓞 D.F) (z : (Obar p).toSubring), (z : PadicAlgCl p) = G.emb (L.w i) (L.e c) →
      red z = β (b.t i c)

structure Frame (T : Theory p) (red : (Obar p).toSubring →+* k) (r : ℕ) (H : PDivGroup p k) (act : D.O → (H ⟶ H))
    (rat : ℤ → (H ⟶ H) → Prop) (d : (w : Fin G.m) → GL (Fin G.n) (KQ p (G.Fw w) r)) where

  io : GlobalTheory.LKLoc.intR p (Q0 p) r →+* WittVector p k
  io_red : ∀ (a : GlobalTheory.LKLoc.intR p (Q0 p) r) (z : (Obar p).toSubring),
    (z : PadicAlgCl p) = ((a : Qr p r) : PadicAlgCl p) → WittVector.constantCoeff (io a) = red z

  sp : ∀ w, D.O →+* Matrix (Fin D.m) (Fin D.m) (intKQ p (G.Fw w) r)
  sp_F : ∀ w (c : 𝓞 D.F), (sp w (algebraMap (𝓞 D.F) D.O c)).map (intKQ p (G.Fw w) r).subtype =
    Matrix.scalar (Fin D.m) (inclK p (G.Fw w) r (G.embW w (L.e c)))

  B : ∀ w, Matrix (Fin D.m) (Fin G.n) (intKQ p (G.Fw w) r) →+ T.M H
  B_smul : ∀ w (a : GlobalTheory.LKLoc.intR p (Q0 p) r) (a' : intKQ p (G.Fw w) r), (a' : KQ p (G.Fw w) r) = inclQ p (G.Fw w) r a →
    ∀ X, B w (a' • X) = io a • B w X
  B_act : ∀ w c X, T.map (act c) (B w X) = B w ((sp w c)ᵀ * X)
  B_span : Submodule.span (WittVector p k) (⋃ w, Set.range (B w)) =
    LinearMap.ker (T.map (act (algebraMap (𝓞 D.F) D.O D.ω)) - GlobalTheory.IsogParam.zpW p k L.ρp • LinearMap.id)
  B_rat : ∀ w m ψ X, rat m ψ → T.map ψ (B w X) = m • (fun x => T.F H x)^[r] (B w X)
  B_F : ∀ w X, ∃ Y : Matrix (Fin D.m) (Fin G.n) (intKQ p (G.Fw w) r), Y.map (intKQ p (G.Fw w) r).subtype =
    HMul.hMul (α := Matrix (Fin D.m) (Fin G.n) (KQ p (G.Fw w) r)) (β := Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) r))
      ((X.map (intKQ p (G.Fw w) r).subtype).map (sigKQ p (G.Fw w) r)) ((d w)⁻¹).val ∧ T.F H (B w X) = B w Y

def IsDelta (T : Theory p) (red : (Obar p).toSubring →+* k) (r : ℕ) (o : Obj b N (spMap β)) (π : End0 (av o))
    (d : (w : Fin G.m) → GL (Fin G.n) (KQ p (G.Fw w) r)) : Prop :=
  ∃ (H : PDivGroup p k) (t : H.TorsionTower (av o).X),
    Nonempty (Frame L T red r H (fun c => t.map t (actEnd o c).hom)
      (fun m ψ => ∃ g : End (av o), m • π = toEnd0 _ g ∧ ψ = t.map t g.hom) d)

def IsPair (T : Theory p) (red : (Obar p).toSubring →+* k) (r : ℕ) (o : Obj b N (spMap β)) (π : End0 (av o))
    (ga : G.GAf) (δ : Gr G r) : Prop :=
  IsGamma L o π ga⁻¹ ∧ IsDelta L T red r o π δ.2 ∧
    ∃ c : ℚ, ((uSimR (AfP p) ga : (AfP p)ˣ) : AfP p) = algebraMap ℚ (AfP p) c ∧
      (((GlobalTheory.LKLoc.nrm p (Q0 p) 1 r δ.1).val 0 0 : Qr p r) : PadicAlgCl p) = (c : PadicAlgCl p)

def weight (T : Theory p) (red : (Obar p).toSubring →+* k) (r : ℕ) (f : G.GAf → ℂ) (φ : Gr G r → ℂ)
    (o : Obj b N (spMap β)) (π : End0 (av o)) : ℂ :=
  if h : ∃ x : G.GAf × Gr G r, IsPair L T red r o π x.1 x.2 then f h.choose.1 * φ h.choose.2 else 0

def geomSum (T : Theory p) (b : Base D R) (β : R →+* k) (red : (Obar p).toSubring →+* k) (N r : ℕ) (f : G.GAf → ℂ)
    (φ : Gr G r → ℂ) : ℂ :=
  ∑ᶠ q : Pts b β N, ∑ᶠ π : End0 (av (Quot.out q)), weight L T red r f φ (Quot.out q) π

end Points

structure Setup {D : Datum p} {G : HTGroup p} (L : Link D G) {R : Type} [CommRing R] (b : Base D R)
    (β : R →+* AlgebraicClosure (ZMod p)) (red : (Obar p).toSubring →+* AlgebraicClosure (ZMod p)) (N r : ℕ) : Prop where
  simple : D.IsSimple
  div : HasDivPlace G
  three : 3 ≤ N
  cop : N.Coprime p
  pos : 0 < r
  rat : ∀ x, β x ^ p ^ r = β x
  compat : Compat L b β red

structure Tests {D : Datum p} {G : HTGroup p} (L : Link D G) (N r : ℕ) (f : G.GAf → ℂ) (φ : Gr G r → ℂ) : Prop where
  test : IsTest (MonoidHom.id _) (L.KN N) (L.KN N) f
  reg : ∀ ga, f ga ≠ 0 → RegAf G ga
  inv : ∀ k ∈ KHT p G.m G.n r G.Fw, ∀ δ, φ (k⁻¹ * δ * sigG G r k) = φ δ
  supp : ∀ δ, φ δ ≠ 0 → L.MuSupp r δ

def GeoCount : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R]
    (b : Base D R) (β : R →+* AlgebraicClosure (ZMod p)) (red : (Obar p).toSubring →+* AlgebraicClosure (ZMod p))
    (N r : ℕ), Setup L b β red N r → ∀ (f : G.GAf → ℂ) (φ : Gr G r → ℂ), Tests L N r f φ →
    ∀ sel, L.GoodSel sel →
      geomSum L T b β red N r f φ = markedSum G (fun _ => 1) sel (L.KN N) f r (KHT p G.m G.n r G.Fw) φ

def FixBridge : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R]
    (b : Base D R) (β : R →+* AlgebraicClosure (ZMod p)) (red : (Obar p).toSubring →+* AlgebraicClosure (ZMod p))
    (N N' r : ℕ), Setup L b β red N r → N ∣ N' → N'.Coprime p → ∀ (g : G.GAf),
    (∀ k ∈ L.KN N', g * k * g⁻¹ ∈ L.KN N) →
    ∀ (M : Model b N) (M' : Model b N') (q₁ q₂ : M'.X ⟶ M.X), IsHecke L β M' M q₁ 1 → IsHecke L β M' M q₂ g →
    ∀ (y : Sp (AlgebraicClosure (ZMod p)) ⟶ M'.X) (o : Obj b N' (spMap β)), Classifies M' y o →
      (y ≫ q₂ = spMap (iterateFrobenius (AlgebraicClosure (ZMod p)) p r) ≫ y ≫ q₁ ↔
        ∃ π ga δ, IsPair L T red r o π ga δ ∧ L.MuSupp r δ ∧ ga * g⁻¹ ∈ L.KN N) ∧
      ∀ π ga δ π' ga' δ', IsPair L T red r o π ga δ → L.MuSupp r δ → ga * g⁻¹ ∈ L.KN N →
        IsPair L T red r o π' ga' δ' → L.MuSupp r δ' → ga' * g⁻¹ ∈ L.KN N → π = π'

end GlobalTheory.LKGeo
