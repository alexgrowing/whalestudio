import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericHeckeMap
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsGHeckeMapForget

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

section

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {R : Type} [CommRing R] [Algebra ℚ R]
  {gb : GBase D.toG R} {S : Scheme.{0}} {s : S ⟶ Sp R}

private theorem comp_pow_overScheme_grpObj {A T T' : Over S} [GrpObj A] (f : T' ⟶ T) (x : T ⟶ A) (n : ℕ) :
    f ≫ x ^ n = (f ≫ x) ^ n := MonObj.comp_pow x n f

private theorem pow_comp_monHom_overScheme_grpObj {A B T : Over S} [GrpObj A] [GrpObj B] (φ : A ⟶ B) [IsMonHom φ] (x : T ⟶ A) (n : ℕ) :
    (x ^ n) ≫ φ = (x ≫ φ) ^ n := MonObj.pow_comp x n φ

private theorem pt_transfer {N' N : ℕ} (hN : 0 < N) (hNp : N.Coprime p) {o : GObj gb N' s} {o₁ o₂ : GObj gb N s}
    {ψ₁ : o.A ⟶ o₁.A} {ψ₂ : o.A ⟶ o₂.A} {ψ' : o₁.A ⟶ o.A} {d : ℕ} (hψ' : IsMonHom ψ')
    (hd : ψ₁ ≫ ψ' = (𝟙 o.A) ^ d) (hdp : d.Coprime p) {h : G.GAf} {k : Type} [Field k] {t : Sp k ⟶ S}
    (I : UpperTheory.Gal.Int.Geo.TIso o t) (J₁ : UpperTheory.Gal.Int.Geo.TIso o₁ t) (J₂ : UpperTheory.Gal.Int.Geo.TIso o₂ t)
    (H₁ : Rel L I J₁ ψ₁ h) (H₂ : Rel L I J₂ ψ₂ h) (a : Over.mk t ⟶ o.A) (y : D.La)
    (ha : a ≫ ψ₁ = J₁.ev N y) : a ≫ ψ₂ = J₂.ev N y := by
  haveI := hψ'
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | h0
    · rw [Nat.coprime_zero_left] at hdp
      exact absurd hdp (Fact.out : p.Prime).one_lt.ne'
    · exact h0
  have hn : 0 < N * d := Nat.mul_pos hN hd0
  have hnp : (N * d).Coprime p := Nat.Coprime.mul hNp hdp
  have h1 : (a ≫ ψ₁) ^ N = 1 := by
    rw [ha]
    exact (J₁.onto N hN _).mpr ⟨y, rfl⟩
  have h2 : a ^ d = (a ≫ ψ₁) ≫ ψ' := by
    rw [Category.assoc, hd, comp_pow_overScheme_grpObj, Category.comp_id]
  have h3 : a ^ (N * d) = 1 := by
    rw [mul_comm, pow_mul, h2, ← pow_comp_monHom_overScheme_grpObj, h1, MonObj.one_comp]
  obtain ⟨x, hx⟩ := (I.onto (N * d) hn a).mp h3
  let y' : D.toG.La := y
  have hJ₁ : J₁.ev N y' = J₁.ev (N * d) (d • y') := by
    rw [HeckeRestrict.ev_nsmul, J₁.tower N d hN hd0]
  have hJ₂ : J₂.ev N y' = J₂.ev (N * d) (d • y') := by
    rw [HeckeRestrict.ev_nsmul, J₂.tower N d hN hd0]
  change a ≫ ψ₁ = J₁.ev N y' at ha
  change a ≫ ψ₂ = J₂.ev N y'
  rw [← hx] at ha ⊢
  rw [hJ₂]
  rw [hJ₁] at ha
  exact (H₂ (N * d) hn hnp x (d • y')).mpr ((H₁ (N * d) hn hnp x (d • y')).mp ha)

end

theorem UpperTheory.Gal.G3.pTransKer :
    RelComp → TateDiff → TateTwist → TransKer := by
  intro RC TD TT p _ D G L R _ _ gb S s N' N o o₁ o₂ ψ₁ ψ₂ h hint hadm T₁ T₂ k _ _ t
  let β : R →+* k := (Spec.preimage (t ≫ s)).hom
  have hβ : t ≫ s = spMap β := by
    simp [β, spMap, Spec.map_preimage]
  have key : ∀ (q₁ q₂ : GObj gb (↑N) s) (φ₁ : o.A ⟶ q₁.A) (φ₂ : o.A ⟶ q₂.A),
      IsTrans L h o q₁ φ₁ → IsTrans L h o q₂ φ₂ → ∀ (a : Over.mk t ⟶ o.A) (y : D.La),
      a ≫ φ₁ = toUnit (Over.mk t) ≫ q₁.eta y → a ≫ φ₂ = toUnit (Over.mk t) ≫ q₂.eta y := by
    intro q₁ q₂ φ₁ φ₂ U₁ U₂ a y ha
    obtain ⟨-, -, ⟨φ', d, hφ', -, hd, -, hdp⟩, -, tate₁⟩ := U₁
    obtain ⟨hmon₂, -, -, -, tate₂⟩ := U₂
    obtain ⟨I₁, J₁, hI₁, hJ₁, R₁⟩ := tate₁ k t β hβ
    obtain ⟨I₂, J₂, hI₂, hJ₂, R₂⟩ := tate₂ k t β hβ
    obtain ⟨u, hu, hR⟩ := TD p D G L R gb S s N' o k t I₁ I₂ hI₁ hI₂
    have hc₁ := (RC p D G L R gb S s (↑N') (↑N') (↑N) o o q₂ k t I₁ I₂ J₂ (𝟙 _) φ₂ u h
      inferInstance hmon₂ hint).2 hR R₂
    have hw : h * u⁻¹ * h⁻¹ ∈ L.KN ↑N := hadm _ (Subgroup.inv_mem _ hu)
    obtain ⟨J₃, hJ₃, hR₃⟩ := TT p D G L R gb S s N q₂ k t J₂ hJ₂ _ hw
    have hwi : Integ L (h * u⁻¹ * h⁻¹) :=
      UpperTheory.Gal.Int.Geo.integ_of_mem (UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hw)
    have hc₂ := (RC p D G L R gb S s (↑N') (↑N) (↑N) o q₂ q₂ k t I₁ J₂ J₃ (𝟙 _ ≫ φ₂) (𝟙 _) (h * u) _
      inferInstance inferInstance hwi).2 hc₁ hR₃
    have hg : h * u⁻¹ * h⁻¹ * (h * u) = h := by group
    rw [hg, Category.id_comp, Category.comp_id] at hc₂
    have hN : 0 < (N : ℕ) := lt_of_lt_of_le (by norm_num) N.2.1
    rw [hJ₁ y] at ha
    rw [hJ₃ y]
    exact pt_transfer hN N.2.2 hφ' hd hdp I₁ J₁ J₃ R₁ hc₂ a y ha
  have hz : ∀ q : GObj gb (↑N) s, toUnit (Over.mk t) ≫ q.eta (0 : D.La) = 1 := by
    intro q
    rw [show q.eta (0 : D.La) = 1 from q.eta_zero, MonObj.comp_one]
  refine ⟨fun a => ⟨fun h1 => ?_, fun h2 => ?_⟩, fun a y => ⟨key o₁ o₂ ψ₁ ψ₂ T₁ T₂ a y, key o₂ o₁ ψ₂ ψ₁ T₂ T₁ a y⟩⟩
  · have := key o₁ o₂ ψ₁ ψ₂ T₁ T₂ a 0 (by rw [h1, hz])
    rwa [hz] at this
  · have := key o₂ o₁ ψ₂ ψ₁ T₂ T₁ a 0 (by rw [h2, hz])
    rwa [hz] at this
