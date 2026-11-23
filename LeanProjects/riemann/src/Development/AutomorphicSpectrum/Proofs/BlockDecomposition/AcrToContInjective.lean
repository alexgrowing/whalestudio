import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingBaseChangeFromUniversalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFunctionsPeriodRingSeparationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousAlgebraUniversalPropertyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLocallyConstantToZModPow

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContLine

variable {l : ℕ} [Fact l.Prime]

theorem toCont_ev (A : PAlg l) (z : ℤ_[l]) : A.toCont ℤ_[l] ≫ A.evCont z = 𝟙 A :=
  Hom.ext (RingHom.ext fun _ => rfl)

theorem shift_ev (A : PAlg l) (z : ℤ_[l]) : contShift A ≫ A.evCont z = A.evCont (z + 1) :=
  Hom.ext (RingHom.ext fun _ => rfl)

theorem toCont_shift (A : PAlg l) : A.toCont ℤ_[l] ≫ contShift A = A.toCont ℤ_[l] :=
  Hom.ext (RingHom.ext fun _ => rfl)

theorem toCont_contMap {A B : PAlg l} (φ : A ⟶ B) :
    A.toCont ℤ_[l] ≫ contMap φ ℤ_[l] = φ ≫ B.toCont ℤ_[l] :=
  Hom.ext (RingHom.ext fun _ => rfl)

theorem contMap_id (A : PAlg l) : contMap (𝟙 A) ℤ_[l] = 𝟙 (A.cont ℤ_[l]) :=
  Hom.ext (RingHom.ext fun _ => rfl)

theorem contMap_comp {A B C : PAlg l} (φ : A ⟶ B) (ψ : B ⟶ C) :
    contMap (φ ≫ ψ) ℤ_[l] = contMap φ ℤ_[l] ≫ contMap ψ ℤ_[l] :=
  Hom.ext (RingHom.ext fun _ => rfl)

theorem contMap_shift {A B : PAlg l} (φ : A ⟶ B) :
    contMap φ ℤ_[l] ≫ contShift B = contShift A ≫ contMap φ ℤ_[l] :=
  Hom.ext (RingHom.ext fun _ => rfl)

def Xi (P : PAlg l ⥤ Type) : P.Elements ⥤ P.Elements where
  obj T := ⟨T.1.cont ℤ_[l], P.map (T.1.toCont ℤ_[l]) T.2⟩
  map {T T'} φ := ⟨contMap φ.1 ℤ_[l], by
    rw [← Functor.map_comp_apply, toCont_contMap, Functor.map_comp_apply, φ.2]⟩
  map_id T := Subtype.ext (contMap_id T.1)
  map_comp φ ψ := Subtype.ext (contMap_comp φ.1 ψ.1)

def iota (P : PAlg l ⥤ Type) : 𝟭 P.Elements ⟶ Xi P where
  app T := ⟨T.1.toCont ℤ_[l], rfl⟩
  naturality T T' φ := Subtype.ext (toCont_contMap φ.1).symm

def gam (P : PAlg l ⥤ Type) : Xi P ⟶ Xi P where
  app T := ⟨contShift T.1, by
    change P.map (contShift T.1) (P.map (T.1.toCont ℤ_[l]) T.2) = P.map (T.1.toCont ℤ_[l]) T.2
    rw [← Functor.map_comp_apply, toCont_shift]⟩
  naturality T T' φ := Subtype.ext (contMap_shift φ.1)

def eta₀ (ε : Eps l) : (((base l).cont ℤ_[l]).A)ˣ := (GlobalTheory.T.continuous_algebra_universal_property ε).choose

theorem eta₀_sharp (ε : Eps l) : ((base l).cont ℤ_[l]).sharp (eta₀ ε) = 1 :=
  (GlobalTheory.T.continuous_algebra_universal_property ε).choose_spec.1

theorem eta₀_shift (ε : Eps l) :
    PAlg.Hom.f (contShift (base l)) (eta₀ ε) = ((base l).cont ℤ_[l]).s (ε.e 0) * eta₀ ε :=
  (GlobalTheory.T.continuous_algebra_universal_property ε).choose_spec.2.1

theorem eta₀_univ (ε : Eps l) (A t : PAlg l) (ht : t.IsTest) (φ : A ⟶ t) (u : (t.A)ˣ) (hu : t.sharp u = 1) :
    ∃! ψ : A.cont ℤ_[l] ⟶ t, A.toCont ℤ_[l] ≫ ψ = φ ∧
      PAlg.Hom.f ψ (PAlg.Hom.f (contMap A.fromBase ℤ_[l]) (eta₀ ε)) = u :=
  (GlobalTheory.T.continuous_algebra_universal_property ε).choose_spec.2.2 A t ht φ u hu

def eta (ε : Eps l) (A : PAlg l) : ((A.cont ℤ_[l]).A)ˣ :=
  Units.map (PAlg.Hom.f (contMap A.fromBase ℤ_[l])).toMonoidHom (eta₀ ε)

theorem eta_val (ε : Eps l) (A : PAlg l) :
    ((eta ε A : ((A.cont ℤ_[l]).A)ˣ) : (A.cont ℤ_[l]).A) = PAlg.Hom.f (contMap A.fromBase ℤ_[l]) (eta₀ ε) := rfl

theorem eta_sharp (ε : Eps l) (A : PAlg l) : (A.cont ℤ_[l]).sharp (eta ε A) = 1 := by
  rw [eta_val, ← mapU_sharp, eta₀_sharp, map_one]

theorem eta_map (ε : Eps l) {A B : PAlg l} (φ : A ⟶ B) :
    PAlg.Hom.f (contMap φ ℤ_[l]) (eta ε A) = eta ε B := by
  rw [eta_val, eta_val, ← fromBase_comp A φ, contMap_comp]
  rfl

theorem eta_shift (ε : Eps l) (A : PAlg l) :
    PAlg.Hom.f (contShift A) (eta ε A) = (A.cont ℤ_[l]).s (ε.e 0) * eta ε A := by
  have h : PAlg.Hom.f (contShift A) (PAlg.Hom.f (contMap A.fromBase ℤ_[l]) (eta₀ ε)) =
      PAlg.Hom.f (contMap A.fromBase ℤ_[l]) (PAlg.Hom.f (contShift (base l)) (eta₀ ε)) :=
    congrArg (fun f => PAlg.Hom.f f (eta₀ ε)) (contMap_shift A.fromBase).symm ▸ rfl
  rw [eta_val, h, eta₀_shift, map_mul]
  exact congrArg (· * _) (RingHom.congr_fun (Hom.comm (contMap A.fromBase ℤ_[l])) (ε.e 0 : Ob l))

def line (ε : Eps l) (P : PAlg l ⥤ Type) : Line (jE P) (epsU ε P) where
  Ξ := Xi P
  i := iota P
  η T := ⟨eta ε T.1, MonoidHom.mem_ker.2 (Units.ext (eta_sharp ε T.1))⟩
  map_η φ := Subtype.ext (Units.ext (eta_map ε φ.1))
  γ := gam P
  iγ := NatTrans.ext (funext fun T => Subtype.ext (toCont_shift T.1))
  γη T := Subtype.ext (Units.ext (eta_shift ε T.1))
  univ T t φ a := by
    have ha : t.1.obj.sharp (a.1).1 = 1 := congrArg Units.val (MonoidHom.mem_ker.1 a.2)
    obtain ⟨ψ, ⟨h1, h2⟩, hu⟩ := eta₀_univ ε T.1 t.1.obj t.1.property φ.1 a.1 ha
    have hψ : P.map ψ (P.map (T.1.toCont ℤ_[l]) T.2) = t.2 := by
      rw [← Functor.map_comp_apply, h1]
      exact φ.2
    refine ⟨⟨ψ, hψ⟩, ⟨Subtype.ext h1, Subtype.ext (Units.ext h2)⟩, ?_⟩
    rintro ⟨ψ', h'⟩ ⟨e1, e2⟩
    refine Subtype.ext (hu ψ' ⟨congrArg Subtype.val e1, ?_⟩)
    exact congrArg (fun x => (x.1).1) e2

theorem acr_ev_const (A : PAlg l) (n : ℕ) (z : ℤ_[l]) (a : A.Acr n) :
    mapAcr (A.evCont z) n (mapAcr (A.toCont ℤ_[l]) n a) = a := by
  rw [← mapAcr_comp, toCont_ev, mapAcr_id]

theorem acr_ev_shift (A : PAlg l) (n : ℕ) (z : ℤ_[l]) (x : (A.cont ℤ_[l]).Acr n) :
    mapAcr (A.evCont z) n (mapAcr (contShift A) n x) = mapAcr (A.evCont (z + 1)) n x := by
  rw [← mapAcr_comp, shift_ev]

theorem acr_toCont_injective (A : PAlg l) (n : ℕ) : Function.Injective (mapAcr (A.toCont ℤ_[l]) n) :=
  Function.LeftInverse.injective (g := mapAcr (A.evCont 0) n) (acr_ev_const A n 0)

theorem map_mem_map {A B : PAlg l} (f : A ⟶ B) (n : ℕ) (𝔞 : Ideal ((base l).Acr n)) {x : A.Acr n}
    (hx : x ∈ 𝔞.map (mapAcr A.fromBase n)) : mapAcr f n x ∈ 𝔞.map (mapAcr B.fromBase n) := by
  have h : 𝔞.map (mapAcr A.fromBase n) ≤ (𝔞.map (mapAcr B.fromBase n)).comap (mapAcr f n) :=
    Ideal.map_le_iff_le_comap.2 fun a ha => by
      rw [Ideal.mem_comap, Ideal.mem_comap, mapAcr_fromBase]
      exact Ideal.mem_map_of_mem _ ha
  exact h hx

theorem fixed_const (A : PAlg l) (n : ℕ) (𝔞 : Ideal ((base l).Acr n)) {x : (A.cont ℤ_[l]).Acr n}
    (hx : x ∈ 𝔞.map (mapAcr (A.cont ℤ_[l]).fromBase n)) (hg : mapAcr (contShift A) n x = x) :
    ∃ m ∈ 𝔞.map (mapAcr A.fromBase n), mapAcr (A.toCont ℤ_[l]) n m = x := by
  obtain ⟨hlc, hinj, -⟩ := GlobalTheory.T.continuous_functions_period_ring_separation A n
  have hper : ∀ z, mapAcr (A.evCont z) n x = mapAcr (A.evCont 0) n x :=
    GlobalTheory.CompanionTheory.PadicShift.eq_of_shift_invariant l _ (hlc x) fun z => by
      rw [← acr_ev_shift, hg]
  refine ⟨mapAcr (A.evCont 0) n x, map_mem_map _ n 𝔞 hx, ?_⟩
  rw [← sub_eq_zero]
  refine hinj _ fun z => ?_
  rw [map_sub, acr_ev_const, hper z, sub_self]

theorem shift_surj (A : PAlg l) (n : ℕ) (𝔞 : Ideal ((base l).Acr n)) {x : (A.cont ℤ_[l]).Acr n}
    (hx : x ∈ 𝔞.map (mapAcr (A.cont ℤ_[l]).fromBase n)) :
    ∃ y ∈ 𝔞.map (mapAcr (A.cont ℤ_[l]).fromBase n), mapAcr (contShift A) n y - y = x := by
  obtain ⟨hlc, hinj, hex⟩ := GlobalTheory.T.continuous_functions_period_ring_separation A n
  let f : ℤ_[l] → ↥(𝔞.map (mapAcr A.fromBase n)) := fun z =>
    ⟨mapAcr (A.evCont z) n x, map_mem_map _ n 𝔞 hx⟩
  have hf : IsLocallyConstant f := by
    refine (IsLocallyConstant.iff_eventually_eq f).2 fun z => ?_
    filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 (hlc x) z] with w hw
    exact Subtype.ext hw
  have hN : ∀ a : ↥(𝔞.map (mapAcr A.fromBase n)), l ^ n • a = 0 := fun a => Subtype.ext (by
    change l ^ n • (a.1 : A.Acr n) = 0
    rw [nsmul_eq_mul, Nat.cast_pow, A.pow_l_acr n, zero_mul])
  obtain ⟨y, hy, hd⟩ := GlobalTheory.CompanionTheory.PadicShift.exists_primitive l n hN f hf
  obtain ⟨w, hw, hwz⟩ := hex 𝔞 (fun z => (y z).1) (hy.comp _) fun z => (y z).2
  refine ⟨w, hw, ?_⟩
  rw [← sub_eq_zero]
  refine hinj _ fun z => ?_
  rw [map_sub, map_sub, acr_ev_shift, hwz, hwz, sub_eq_zero]
  exact congrArg Subtype.val (hd z)

theorem facyc_of {R : Type} [CommRing R] {C : Type*} [Category C] {G : C ⥤ ModuleCat.{0} R} (Φ : Flt G) {T T' : C}
    (i : T ⟶ T') (g : T' ⟶ T') (h1 : Function.Injective (G.map i).hom)
    (h2 : ∀ r, ∀ x ∈ (Φ.S r).S T', (G.map g).hom x = x → ∃ m, m ∈ (Φ.S r).S T ∧ (G.map i).hom m = x)
    (h3 : ∀ r, ∀ x ∈ (Φ.S r).S T', ∃ y, y ∈ (Φ.S r).S T' ∧ (G.map g).hom y - y = x) : Φ.FAcyc i g := by
  refine ⟨h1, fun r x hx hg => ?_, fun r x hx => ?_⟩
  · obtain ⟨m, hm, hmx⟩ := h2 r x hx hg
    exact ⟨_, Φ.mul r T m hm, by rw [map_smul, hmx]⟩
  · obtain ⟨y, hy, hyx⟩ := h3 r x hx
    exact ⟨_, Φ.mul r T' y hy, by rw [map_smul, ← smul_sub, hyx]⟩

section Main

variable {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l) (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ)

theorem mem_step (r : ℕ) (T : (F.pt κ).Elements) (x : T.1.Acr n) :
    x ∈ (((flt F κ ε k n ρ hρ).comap (gE F κ k n)).S r).S T ↔
      x ∈ (fil (DD k (base l) n) (ρ r)).map (mapAcr T.1.fromBase n) := by
  rw [← (GlobalTheory.T.period_ring_base_change_from_universal T.1 n).2.2.2.2.1 k (ρ r)]
  rfl

theorem step_fixed (T : (F.pt κ).Elements) (r : ℕ) (x : (T.1.cont ℤ_[l]).Acr n)
    (hx : x ∈ (((flt F κ ε k n ρ hρ).comap (gE F κ k n)).S r).S ((Xi (F.pt κ)).obj T))
    (hg : mapAcr (contShift T.1) n x = x) :
    ∃ m : T.1.Acr n, m ∈ (((flt F κ ε k n ρ hρ).comap (gE F κ k n)).S r).S T ∧
      mapAcr (T.1.toCont ℤ_[l]) n m = x := by
  obtain ⟨m, hm, hmx⟩ := fixed_const T.1 n _ ((mem_step F κ ε k n ρ hρ r ((Xi (F.pt κ)).obj T) x).1 hx) hg
  exact ⟨m, (mem_step F κ ε k n ρ hρ r T m).2 hm, hmx⟩

theorem step_surj (T : (F.pt κ).Elements) (r : ℕ) (x : (T.1.cont ℤ_[l]).Acr n)
    (hx : x ∈ (((flt F κ ε k n ρ hρ).comap (gE F κ k n)).S r).S ((Xi (F.pt κ)).obj T)) :
    ∃ y : (T.1.cont ℤ_[l]).Acr n, y ∈ (((flt F κ ε k n ρ hρ).comap (gE F κ k n)).S r).S ((Xi (F.pt κ)).obj T) ∧
      mapAcr (contShift T.1) n y - y = x := by
  obtain ⟨y, hy, hyx⟩ := shift_surj T.1 n _ ((mem_step F κ ε k n ρ hρ r ((Xi (F.pt κ)).obj T) x).1 hx)
  exact ⟨y, (mem_step F κ ε k n ρ hρ r ((Xi (F.pt κ)).obj T) y).2 hy, hyx⟩

theorem facyc (T : (F.pt κ).Elements) :
    ((flt F κ ε k n ρ hρ).comap (gE F κ k n)).FAcyc ((line ε (F.pt κ)).i.app T) ((line ε (F.pt κ)).γ.app T) :=
  facyc_of _ _ _ (acr_toCont_injective T.1 n) (fun r x hx hg => step_fixed F κ ε k n ρ hρ T r x hx hg)
    (fun r x hx => step_surj F κ ε k n ρ hρ T r x hx)

end Main

theorem exists_line : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l) (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ), ∃ L : Line (jE (F.pt κ)) (epsU ε (F.pt κ)), ∀ T, ((flt F κ ε k n ρ hρ).comap (gE F κ k n)).FAcyc (L.i.app T) (L.γ.app T) :=
  fun F κ ε k n ρ hρ => ⟨line ε (F.pt κ), facyc F κ ε k n ρ hρ⟩

end GlobalTheory.CompanionTheory.ContLine
