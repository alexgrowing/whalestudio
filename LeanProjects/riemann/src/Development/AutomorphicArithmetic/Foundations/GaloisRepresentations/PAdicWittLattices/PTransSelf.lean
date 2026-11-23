import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem pol_one {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] [Algebra ℚ R]
    {gb : GBase D.toG R} {S : Scheme.{0}} {s : S ⟶ Sp R} {N : ℕ} (o : GObj gb N s) :
    Nonempty (LBIso (Hecke.lbPow o.P 1) (o.P.pull (Hecke.sq2 (𝟙 o.A)))) := by
  have h : Hecke.sq2 (𝟙 o.A) = 𝟙 _ := by simp [Hecke.sq2]
  refine ⟨?_⟩
  rw [h]
  unfold Hecke.lbPow LB.pull
  exact (GlobalTheory.PrimNorm.lbIso_iff o.isLB _ _ _ _).2 rfl

private theorem gTateIso_ev_nsmul' {G : GDatum} {k : Type} [Field k] {Q : Type} [Group Q]
    {act : G.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} (I : GTateIso G k Q act e) (n c : ℕ)
    (y : G.La) : I.ev n (c • y) = I.ev n y ^ c := by
  induction c with
  | zero =>
    have h := I.add n 0 0
    rw [add_zero] at h
    have h1 : I.ev n 0 = 1 :=
      mul_left_cancel (a := I.ev n 0) (by rw [_root_.mul_one]; exact h.symm)
    rw [zero_smul, pow_zero, h1]
  | succ c ih => rw [succ_nsmul, I.add, ih, pow_succ]

theorem UpperTheory.Gal.G3.pTransSelf :
    MultBasic → RelComp → TateTwist → TransSelf := by
  intro hM hR hT p _ D G L R _ _ gb S s N
  refine ⟨fun o u hu => ?_, fun c hN hc o => ?_⟩
  · have hu1 : u ∈ L.KN 1 := UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hu
    obtain ⟨a, a', ha, ha', haa, heq⟩ := (hM p).2.2 D G L u hu1
    refine ⟨⟨by simp, by simp⟩, fun _ => by simp, ⟨𝟙 _, 1, ⟨by simp, by simp⟩, fun _ => by simp,
      by simp, by simp, Nat.coprime_one_left _⟩, ⟨1, Nat.coprime_one_left _, pol_one o, a, a', ha,
      ha', haa, heq⟩, ?_⟩
    intro k _ _ x β hβ
    obtain ⟨I, hI⟩ := o.geom k x β hβ
    obtain ⟨J, hJ, hRel⟩ := hT p D G L R gb S s N o k x I hI u hu
    exact ⟨I, J, hI, hJ, hRel⟩
  · obtain ⟨a, a', ha, ha', haa, heq⟩ := (hM p).2.2 D G L 1 (one_mem _)
    have hmon : IsMonHom (𝟙 o.A) := ⟨by simp, by simp⟩
    refine ⟨show IsMonHom (𝟙 o.A) from hmon, fun _ => by simp [GObj.forgetMul],
      ⟨𝟙 _, 1, show IsMonHom (𝟙 o.A) from hmon,
      fun _ => by simp [GObj.forgetMul], by simp; exact Category.comp_id _,
      by simp; exact Category.comp_id _, Nat.coprime_one_left _⟩,
      ⟨1, Nat.coprime_one_left _, pol_one o, a, a', ha, ha', haa, heq⟩, ?_⟩
    intro k _ _ x β hβ
    obtain ⟨I, hI⟩ := o.geom k x β hβ
    have hInt : UpperTheory.Gal.Int.Geo.Integ L 1 := UpperTheory.Gal.Int.Geo.integ_of_mem (one_mem _)
    refine ⟨I, I, hI, fun y => ?_, ?_⟩
    · show toUnit _ ≫ o.eta (c • y) = _
      rw [hI, gTateIso_ev_nsmul', I.tower _ _ hN hc]
    · exact (hR p D G L R gb S s _ _ _ o o o k x I I I (𝟙 _) (𝟙 _) 1 1 hmon hmon hInt).1
