import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.IsUnitWitt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapAcrFromBase
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SchFnPtTw

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg

namespace CrystallineSemistableComparison.Pb

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

namespace Mid

variable (r : Res l K)

def wn (n : ℕ) : Wc.Wm l r.k n →+* (base l).Acr n :=
  Ideal.Quotient.lift _ (((base l).cris n).comp r.w) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [RingHom.comp_apply, map_mul, map_mul, map_pow, map_natCast, map_pow, map_natCast, (base l).pow_l_acr, mul_zero]

theorem wn_mk (n : ℕ) (a : WittVector l r.k) : wn r n (Ideal.Quotient.mk _ a) = (base l).cris n (r.w a) := rfl

theorem im_le (n : ℕ) : Wc.Im l r.k n ≤ (B.JJ true (base l) n).comap (wn r n) := by
  rw [Ideal.map_le_iff_le_comap, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, Ideal.mem_comap,
    wn_mk, map_natCast, map_natCast]
  exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)

def κm (r : Res l K) (n : ℕ) : OK l K →+* (B.bs l true n).R ⧸ (B.bs l true n).I :=
  (Ideal.quotientMap _ (wn r n) (im_le r n)).comp ((Wc.res l r.k n).comp r.ρ)

abbrev Lm (M : Model l K) (n : ℕ) : (B.bs l true n).Fun := (B.schFn M.p).cr (B.bs l true n) rfl (κm r n)

def phiP (l : ℕ) [Fact l.Prime] (n N : ℕ) : (base l).Acr n →+* (base l).Acr n := (base l).phi n ^ N

theorem phiP_succ (n N : ℕ) (x : (base l).Acr n) : phiP l n (N + 1) x = (base l).phi n (phiP l n N x) := by
  rw [phiP, pow_succ']; rfl

theorem dp_phiP (n N : ℕ) : IsDPMorphism (B.DD true (base l) n) (B.DD true (base l) n) (phiP l n N) := by
  induction N with
  | zero => exact ⟨by rw [phiP, pow_zero]; exact (Ideal.map_id _).le, fun _ _ => rfl⟩
  | succ N ih =>
    have e : phiP l n (N + 1) = ((base l).phi n).comp (phiP l n N) := RingHom.ext (phiP_succ n N)
    rw [e]
    exact IsDPMorphism.comp _ ((base l).dpP_phi n) ih

def phiQ (l : ℕ) [Fact l.Prime] (n N : ℕ) : (B.bs l true n).R ⧸ (B.bs l true n).I →+* (B.bs l true n).R ⧸ (B.bs l true n).I :=
  Ideal.quotientMap _ (phiP l n N) (Ideal.map_le_iff_le_comap.1 (dp_phiP (l := l) n N).1)

def TeichmullerCongruence (r : Res l K) (N : ℕ) : Prop := ∀ n (x : OK l K), phiQ l n N (B.κb (okToOC l K) true n x) = κm r n x

theorem phiQ_mk (n N : ℕ) (x : (B.bs l true n).R) :
    phiQ l n N (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (phiP l n N x) := rfl

theorem phiQ_pow (n N : ℕ) (q : (B.bs l true n).R ⧸ (B.bs l true n).I) : phiQ l n N q = q ^ l ^ N := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  induction N generalizing x with
  | zero => rw [phiQ_mk, pow_zero, pow_one]; rfl
  | succ N ih =>
    rw [phiQ_mk, phiP_succ, pow_succ, pow_mul]
    change Ideal.Quotient.mk ((base l).PFil n) ((base l).phi n (phiP l n N x)) = _
    rw [B.phi_mk, ← ih]; rfl

def frbN {B₀ : Type} [CommRing B₀] (h : (l : B₀) = 0) : ℕ → (B₀ →+* B₀)
  | 0 => RingHom.id _
  | N + 1 => (Wc.frb h).comp (frbN h N)

theorem frbN_apply {B₀ : Type} [CommRing B₀] (h : (l : B₀) = 0) (N : ℕ) (x : B₀) : frbN h N x = x ^ l ^ N := by
  induction N with
  | zero => rw [pow_zero, pow_one]; rfl
  | succ N ih =>
    change (frbN h N x) ^ l = _
    rw [ih, pow_succ, pow_mul]

theorem l_zero {B₀ : Type} [CommRing B₀] {n : ℕ} (ψ : (B.bs l true n).R ⧸ (B.bs l true n).I →+* B₀) : (l : B₀) = 0 := by
  rw [← map_natCast ψ, ← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem.2
    (show ((l : (base l).Acr n)) ∈ (B.bs l true n).I from Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)), map_zero]

variable {r} {N : ℕ} (F : B.Fn (OK l K))

def ptIn (n : ℕ) (hT : TeichmullerCongruence r N) : F.ptK (B.κb (okToOC l K) true n) ⟶ F.ptK (κm r n) where
  app B₀ := TypeCat.ofHom fun z => ⟨(z.1.1, F.Pt.map (CommRingCat.ofHom (frbN (l_zero z.1.1) N)) z.1.2), by
    have h := F.ov_map (CommRingCat.ofHom (frbN (l_zero z.1.1) N)) z.2
    have e : (CommRingCat.ofHom (frbN (l_zero z.1.1) N)).hom.comp (z.1.1.comp (B.κb (okToOC l K) true n)) =
        z.1.1.comp (κm r n) := RingHom.ext fun x => by
      change frbN _ N (z.1.1 (B.κb _ true n x)) = z.1.1 (κm r n x)
      rw [frbN_apply, ← map_pow, ← phiQ_pow, hT]
    rwa [e] at h⟩
  naturality B₀ B' φ := by
    ext z
    refine Subtype.ext (Prod.ext rfl ?_)
    change F.Pt.map (CommRingCat.ofHom (frbN (l_zero (φ.hom.comp z.1.1)) N)) (F.Pt.map φ z.1.2) =
      F.Pt.map φ (F.Pt.map (CommRingCat.ofHom (frbN (l_zero z.1.1) N)) z.1.2)
    have e : CommRingCat.ofHom (frbN (l_zero z.1.1) N) ≫ φ = φ ≫ CommRingCat.ofHom (frbN (l_zero (φ.hom.comp z.1.1)) N) :=
      CommRingCat.hom_ext (RingHom.ext fun x => by
        change φ.hom (frbN _ N x) = frbN _ N (φ.hom x)
        rw [frbN_apply, frbN_apply, map_pow])
    have h1 := congrFun (congrArg (fun t => (ConcreteCategory.hom t : _ → _))
      (F.Pt.map_comp (CommRingCat.ofHom (frbN (l_zero z.1.1) N)) φ)) z.1.2
    have h2 := congrFun (congrArg (fun t => (ConcreteCategory.hom t : _ → _))
      (F.Pt.map_comp φ (CommRingCat.ofHom (frbN (l_zero (φ.hom.comp z.1.1)) N)))) z.1.2
    rw [e] at h1
    exact h2.symm.trans h1

def ptOut (n : ℕ) (hT : TeichmullerCongruence r N) : F.ptK (κm r n) ⟶ F.ptK (B.κb (okToOC l K) true n) where
  app B₀ := TypeCat.ofHom fun z => ⟨(z.1.1.comp (phiQ l n N), z.1.2), by
    have e : (z.1.1.comp (phiQ l n N)).comp (B.κb (okToOC l K) true n) = z.1.1.comp (κm r n) :=
      RingHom.ext fun x => congrArg z.1.1 (hT n x)
    rw [e]; exact z.2⟩
  naturality _ _ _ := rfl

variable (r) in

def mIn (M : Model l K) (n : ℕ) (hT : TeichmullerCongruence r N) :
    Mor (Lm r M n) (B.Lc (B.schFn M.p) (okToOC l K) true n) (RingHom.id _) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
    (RingHom.id _) rfl (DPMorphism.id _).isDPMorphism (ptIn (B.schFn M.p) n hT) fun _ _ _ => rfl

variable (r) in

def mOut (M : Model l K) (n : ℕ) (hT : TeichmullerCongruence r N) :
    Mor (B.Lc (B.schFn M.p) (okToOC l K) true n) (Lm r M n) (phiP l n N) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
    (phiP l n N) rfl (dp_phiP n N) (ptOut (B.schFn M.p) n hT) fun _ _ _ => rfl

variable (l) in

def phiA (N : ℕ) : Acris l →+* Acris l := ACris.phi ℂ_[l] l ^ N

theorem phiA_succ (N : ℕ) (a : Acris l) : phiA l (N + 1) a = ACris.phi ℂ_[l] l (phiA l N a) := by
  rw [phiA, pow_succ']; rfl

theorem phiP_cris (n N : ℕ) (a : Acris l) : phiP l n N ((base l).cris n a) = (base l).cris n (phiA l N a) := by
  induction N with
  | zero => rfl
  | succ N ih => rw [phiP_succ, ih, phiA_succ, (base l).phi_cris]

end Mid

end CrystallineSemistableComparison.Pb
