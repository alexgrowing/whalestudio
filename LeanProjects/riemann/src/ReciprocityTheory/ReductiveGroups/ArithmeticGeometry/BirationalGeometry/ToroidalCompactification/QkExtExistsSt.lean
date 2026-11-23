import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfTrivial

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped Pointwise

def QkExtExistsSt : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (D : Out.DegPre R) (F F' : Type) [Field F] [Algebra (FractionRing R) F]
    [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F'),
    (∀ r : FractionRing R, f (algebraMap _ F r) = algebraMap _ F' r) →
    ∀ (k : ℕ) (p : Out.QkPt D F k), ∃ p' : Out.QkPt D F' k, QkExt f p p'

def LevelSpanBSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l)
    (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing k) F]
    (x : Out.TF (R := k) F ⟶ a.D₀.P.A), (letI := H.starRing; ∀ m ∈ l.Mb, x ≫ a.oa.onB.act m = 1) →
    x ∈ Subgroup.closure ({z | ∃ χ, z = toUnit _ ≫ a.D₀.c χ} ∪
      {z | ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ q₀ : Out.QkPt a.D₀ F l.M,
        QkExt (algebraMap (FractionRing k) F) (a.eta v) q₀ ∧ z = q₀.g.b})

theorem coverAlg {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) (N : Type)
    [AddCommGroup N] [Module (𝓞 E) N] (a : N)
    (ha : ∀ m ∈ l.Mb, m • a ∈ ((l.M : 𝓞 E)) • (⊤ : Submodule (𝓞 E) N)) :
    a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) N) := by

  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.coprime]; exact Submodule.mem_top
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp h1

  have hle : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) :=
    Ideal.mul_le_right (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
  rw [l.prod] at hle
  have hM : (l.M : 𝓞 E) ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) :=
    SetLike.le_def.mp hle (Ideal.subset_span (Set.mem_singleton _))
  have hua : u • a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) N) := by
    obtain ⟨b, -, hb⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (ha u hu)
    rw [← hb]
    exact Submodule.smul_mem_smul hM Submodule.mem_top
  have hva : v • a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) N) :=
    Submodule.smul_mem_smul hv Submodule.mem_top
  have key := Submodule.add_mem _ hua hva
  rwa [← add_smul, huv, one_smul] at key

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
