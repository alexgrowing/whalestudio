import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FRatioSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj

theorem mem_of_algebraMap_mem_map_away {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (s : R)
    [IsLocalization.Away s S] {I m : Ideal R} (hm : m.IsMaximal) (hI : m ^ 2 ≤ I) (hs : s ∉ m) {x : R}
    (hx : algebraMap R S x ∈ I.map (algebraMap R S)) : x ∈ I := by
  obtain ⟨⟨y, t⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers s) S).1 hx
  rw [← map_mul] at e
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers s) S).1 e
  have hw : ((c : R) * t) * x ∈ I := by
    have : (c : R) * y ∈ I := I.mul_mem_left _ y.2
    rw [← hc] at this
    convert this using 1; ring
  have hwm : (c : R) * t ∉ m := by
    obtain ⟨k, hk⟩ := c.2
    obtain ⟨l, hl⟩ := t.2
    rw [← hk, ← hl, ← pow_add]
    exact fun h => hs (hm.isPrime.mem_of_pow_mem _ h)
  obtain ⟨u, i, hi, h1⟩ := hm.exists_inv hwm
  have hi2 : i ^ 2 ∈ I := hI (Ideal.pow_mem_pow hi 2)
  have hx' : x = (u ^ 2 * ((c : R) * t) + 2 * u * i) * (((c : R) * t) * x) + x * i ^ 2 := by
    linear_combination (-x * (u * ((c : R) * t) + i + 1)) * h1
  rw [hx']
  exact I.add_mem (I.mul_mem_left _ hw) (I.mul_mem_left _ hi2)

theorem ker_le_map_ker_away {R S K : Type} [CommRing R] [CommRing S] [Field K] [Algebra R S] (s : R)
    [IsLocalization.Away s S] (evR : R →+* K) (evS : S →+* K) (h : ∀ x, evS (algebraMap R S x) = evR x) :
    RingHom.ker evS ≤ (RingHom.ker evR).map (algebraMap R S) := by
  intro w hw
  obtain ⟨⟨x, t⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) w
  dsimp only at hw ⊢
  have hx : evR x = 0 := by
    have := congrArg evS (IsLocalization.mk'_spec S x t)
    rw [map_mul, RingHom.mem_ker.1 hw, zero_mul, h] at this
    exact this.symm
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hx)

theorem span_ratio_of_span_ratio (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (N : ℕ) (ι : X ⟶ PSpace ℂ N)
    (hι : IsClosedImmersion ι) (n : ℕ) (hn : 0 < n) (k : ℕ) (f : Fin k → MvPolynomial (Fin (N + 1)) ℂ)
    (a b : MvPolynomial (Fin (N + 1)) ℂ)
    (hf : ∀ j, f j ∈ GlobalTheory.ProjSpace.grading ℂ N n) (ha : a ∈ GlobalTheory.ProjSpace.grading ℂ N n)
    (hb : b ∈ GlobalTheory.ProjSpace.grading ℂ N n) (z : CxPts p (RingHom.id ℂ))
    (hza : z ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι a))
    (hzb : z ∈ CxPts.ptsIn p (RingHom.id ℂ) (GlobalTheory.EtProj.fOpen ι b))
    (h : RingHom.ker (CxPts.evHom hza) ≤ Ideal.span (Set.range fun j => GlobalTheory.EtProj.fRatio ι (f j) a (hf j) ha) ⊔
          RingHom.ker (CxPts.evHom hza) ^ 2) :
    RingHom.ker (CxPts.evHom hzb) ≤ Ideal.span (Set.range fun j => GlobalTheory.EtProj.fRatio ι (f j) b (hf j) hb) ⊔
          RingHom.ker (CxPts.evHom hzb) ^ 2 := by
  haveI := hι
  set 𝒜 := ProjSpace.grading ℂ N
  set D := Proj.basicOpen 𝒜 a ⊓ Proj.basicOpen 𝒜 b with hDdef
  set W : X.Opens := ι ⁻¹ᵁ D with hWdef
  have hWa : W ≤ fOpen ι a := fun x hx => hx.1
  have hWb : W ≤ fOpen ι b := fun x hx => hx.2
  have hzW : z ∈ CxPts.ptsIn p (RingHom.id ℂ) W :=
    CxPts.mem_ptsIn.2 ⟨CxPts.mem_ptsIn.1 hza, CxPts.mem_ptsIn.1 hzb⟩
  have hUa : IsAffineOpen (fOpen ι a) := (Proj.isAffineOpen_basicOpen 𝒜 a ha hn).preimage ι
  have hUb : IsAffineOpen (fOpen ι b) := (Proj.isAffineOpen_basicOpen 𝒜 b hb hn).preimage ι
  have hres : ∀ {c d : MvPolynomial (Fin (N + 1)) ℂ} (hc : c ∈ 𝒜 n) (hd : d ∈ 𝒜 n) (hW : W ≤ fOpen ι d)
      (hD : D ≤ Proj.basicOpen 𝒜 d),
      resG X hW (fRatio ι c d hc hd) = (ι.app D).hom (ProjFrac.frac 𝒜 D c d hc hd hD) := by
    intro c d hc hd hW hD
    have := congrArg (fun φ => φ.hom (ProjFrac.frac 𝒜 _ c d hc hd le_rfl)) (ι.naturality (homOfLE hD).op)
    simp only [CommRingCat.comp_apply] at this
    rw [← ProjFrac.resG_frac hD]
    exact this.symm

  have hratio : ∀ j, resG X hWa (fRatio ι (f j) a (hf j) ha) =
      resG X hWb (fRatio ι (f j) b (hf j) hb) * (ι.app D).hom (ProjFrac.frac 𝒜 D b a hb ha inf_le_left) := by
    intro j
    rw [hres _ _ hWa inf_le_left, hres _ _ hWb inf_le_right, ← map_mul]
    congr 1
    exact (ProjFrac.frac_mul_eq (by ring)).symm

  set sa := fRatio ι b a hb ha
  set sb := fRatio ι a b ha hb
  have eA : W = X.basicOpen sa := by
    rw [show sa = (ι.app _).hom (ProjFrac.frac 𝒜 _ b a hb ha le_rfl) from rfl]
    refine Eq.trans ?_ (Scheme.preimage_basicOpen ι _)
    rw [ProjFrac.basicOpen_frac]
  have eB : W = X.basicOpen sb := by
    rw [show sb = (ι.app _).hom (ProjFrac.frac 𝒜 _ a b ha hb le_rfl) from rfl]
    refine Eq.trans ?_ (Scheme.preimage_basicOpen ι _)
    rw [ProjFrac.basicOpen_frac]
    exact congrArg (fun U => ι ⁻¹ᵁ U) (inf_comm _ _)
  letI algA : Algebra Γ(X, fOpen ι a) Γ(X, W) := (resG X hWa).toAlgebra
  letI algB : Algebra Γ(X, fOpen ι b) Γ(X, W) := (resG X hWb).toAlgebra
  haveI locA : IsLocalization.Away sa Γ(X, W) := hUa.isLocalization_of_eq_basicOpen sa (homOfLE hWa) eA
  haveI locB : IsLocalization.Away sb Γ(X, W) := hUb.isLocalization_of_eq_basicOpen sb (homOfLE hWb) eB
  have evA : ∀ g, CxPts.evHom hzW (algebraMap Γ(X, fOpen ι a) Γ(X, W) g) = CxPts.evHom hza g := fun g => by
    change CxPts.evHom hzW (resG X hWa g) = _
    rw [← CxPts.ev_eq, ← CxPts.ev_eq]
    exact CxPts.ev_res hWa hzW g
  have evB : ∀ g, CxPts.evHom hzW (algebraMap Γ(X, fOpen ι b) Γ(X, W) g) = CxPts.evHom hzb g := fun g => by
    change CxPts.evHom hzW (resG X hWb g) = _
    rw [← CxPts.ev_eq, ← CxPts.ev_eq]
    exact CxPts.ev_res hWb hzW g
  have h1A := ker_le_map_ker_away sa _ _ evA
  have h1B := ker_le_map_ker_away sb _ _ evB
  have h2A : (RingHom.ker (CxPts.evHom hza)).map (algebraMap Γ(X, fOpen ι a) Γ(X, W)) ≤ RingHom.ker (CxPts.evHom hzW) :=
    Ideal.map_le_iff_le_comap.2 fun x hx => by
      rw [Ideal.mem_comap, RingHom.mem_ker, evA]; exact hx
  have h3 : RingHom.ker (CxPts.evHom hzW) ≤
      Ideal.span ((algebraMap Γ(X, fOpen ι a) Γ(X, W)) '' Set.range fun j => fRatio ι (f j) a (hf j) ha) ⊔
        RingHom.ker (CxPts.evHom hzW) ^ 2 := by
    intro x hx
    have := Ideal.map_mono h (h1A hx)
    rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span] at this
    exact sup_le_sup le_rfl (Ideal.pow_right_mono h2A 2) this
  have h4 : Ideal.span ((algebraMap Γ(X, fOpen ι a) Γ(X, W)) '' Set.range fun j => fRatio ι (f j) a (hf j) ha) ≤
      Ideal.span ((algebraMap Γ(X, fOpen ι b) Γ(X, W)) '' Set.range fun j => fRatio ι (f j) b (hf j) hb) := by
    rw [Ideal.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    change resG X hWa _ ∈ _
    rw [hratio j]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, ⟨j, rfl⟩, rfl⟩)

  have hsurj : Function.Surjective (CxPts.evHom hzb) := fun c =>
    ⟨ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (fOpen ι b) c, by rw [← CxPts.ev_eq]; exact CxPts.ev_algX hzb c⟩
  have hmax : (RingHom.ker (CxPts.evHom hzb)).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj
  have hs : sb ∉ RingHom.ker (CxPts.evHom hzb) := by
    rw [RingHom.mem_ker, ← CxPts.ev_eq]
    exact (CxPts.mem_ptsIn_basicOpen hzb sb).1 (eB ▸ hzW)
  intro g hg
  refine mem_of_algebraMap_mem_map_away (S := Γ(X, W)) sb hmax le_sup_right hs ?_
  have hgW : algebraMap Γ(X, fOpen ι b) Γ(X, W) g ∈ RingHom.ker (CxPts.evHom hzW) := by
    rw [RingHom.mem_ker, evB]; exact hg
  rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span]
  exact sup_le_sup h4 (Ideal.pow_right_mono h1B 2) (h3 hgW)

end GlobalTheory.EtProj
